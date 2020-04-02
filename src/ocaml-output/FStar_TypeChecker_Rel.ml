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
          FStar_Util.format2 "UNIV %s %s" x uu____1023
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
          FStar_Util.format2 "TERM %s %s" x uu____1041
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1060 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1060 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1081 =
      let uu____1085 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1085
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1081 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1104 .
    (FStar_Syntax_Syntax.term * 'Auu____1104) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1123 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1144  ->
              match uu____1144 with
              | (x,uu____1151) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1123 (FStar_String.concat " ")
  
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
        (let uu____1191 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1191
         then
           let uu____1196 = FStar_Thunk.force reason  in
           let uu____1199 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1196 uu____1199
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1222 = mklstr (fun uu____1225  -> reason)  in
        giveup env uu____1222 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1231  ->
    match uu___3_1231 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1237 .
    'Auu____1237 FStar_TypeChecker_Common.problem ->
      'Auu____1237 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___150_1249 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___150_1249.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___150_1249.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___150_1249.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___150_1249.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___150_1249.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___150_1249.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___150_1249.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1257 .
    'Auu____1257 FStar_TypeChecker_Common.problem ->
      'Auu____1257 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1277  ->
    match uu___4_1277 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1283  -> FStar_TypeChecker_Common.TProb _1283)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1289  -> FStar_TypeChecker_Common.CProb _1289)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1295  ->
    match uu___5_1295 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___162_1301 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___162_1301.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___162_1301.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___162_1301.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___162_1301.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___162_1301.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___162_1301.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___162_1301.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___162_1301.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___162_1301.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___166_1309 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___166_1309.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___166_1309.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___166_1309.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___166_1309.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___166_1309.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___166_1309.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___166_1309.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___166_1309.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___166_1309.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1322  ->
      match uu___6_1322 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1329  ->
    match uu___7_1329 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1342  ->
    match uu___8_1342 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1357  ->
    match uu___9_1357 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1372  ->
    match uu___10_1372 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1386  ->
    match uu___11_1386 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1400  ->
    match uu___12_1400 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1412  ->
    match uu___13_1412 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1428 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1428) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1458 =
          let uu____1460 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1460  in
        if uu____1458
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1497)::bs ->
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
          let uu____1544 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1568 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1568]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1544
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1596 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1620 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1620]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1596
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____1667 =
          let uu____1669 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1669  in
        if uu____1667
        then ()
        else
          (let uu____1674 =
             let uu____1677 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____1677
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____1674 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____1726 =
          let uu____1728 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1728  in
        if uu____1726
        then ()
        else
          (let uu____1733 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____1733)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____1753 =
        let uu____1755 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____1755  in
      if uu____1753
      then ()
      else
        (let msgf m =
           let uu____1769 =
             let uu____1771 =
               let uu____1773 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____1773 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____1771  in
           Prims.op_Hat msg uu____1769  in
         (let uu____1778 = msgf "scope"  in
          let uu____1781 = p_scope prob  in
          def_scope_wf uu____1778 (p_loc prob) uu____1781);
         (let uu____1793 = msgf "guard"  in
          def_check_scoped uu____1793 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____1800 = msgf "lhs"  in
                def_check_scoped uu____1800 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1803 = msgf "rhs"  in
                def_check_scoped uu____1803 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____1810 = msgf "lhs"  in
                def_check_scoped_comp uu____1810 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____1813 = msgf "rhs"  in
                def_check_scoped_comp uu____1813 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___259_1834 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___259_1834.wl_deferred);
          ctr = (uu___259_1834.ctr);
          defer_ok = (uu___259_1834.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___259_1834.umax_heuristic_ok);
          tcenv = (uu___259_1834.tcenv);
          wl_implicits = (uu___259_1834.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____1842 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1842 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___263_1865 = empty_worklist env  in
      let uu____1866 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____1866;
        wl_deferred = (uu___263_1865.wl_deferred);
        ctr = (uu___263_1865.ctr);
        defer_ok = (uu___263_1865.defer_ok);
        smt_ok = (uu___263_1865.smt_ok);
        umax_heuristic_ok = (uu___263_1865.umax_heuristic_ok);
        tcenv = (uu___263_1865.tcenv);
        wl_implicits = (uu___263_1865.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___268_1887 = wl  in
        {
          attempting = (uu___268_1887.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___268_1887.ctr);
          defer_ok = (uu___268_1887.defer_ok);
          smt_ok = (uu___268_1887.smt_ok);
          umax_heuristic_ok = (uu___268_1887.umax_heuristic_ok);
          tcenv = (uu___268_1887.tcenv);
          wl_implicits = (uu___268_1887.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____1914 = FStar_Thunk.mkv reason  in defer uu____1914 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___276_1933 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___276_1933.wl_deferred);
         ctr = (uu___276_1933.ctr);
         defer_ok = (uu___276_1933.defer_ok);
         smt_ok = (uu___276_1933.smt_ok);
         umax_heuristic_ok = (uu___276_1933.umax_heuristic_ok);
         tcenv = (uu___276_1933.tcenv);
         wl_implicits = (uu___276_1933.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____1947 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____1947 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____1981 = FStar_Syntax_Util.type_u ()  in
            match uu____1981 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____1993 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____1993 with
                 | (uu____2011,tt,wl1) ->
                     let uu____2014 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2014, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2020  ->
    match uu___14_2020 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2026  -> FStar_TypeChecker_Common.TProb _2026) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2032  -> FStar_TypeChecker_Common.CProb _2032) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2040 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2040 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2060  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2102 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2102 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2102 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2102 FStar_TypeChecker_Common.problem *
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
                        let uu____2189 =
                          let uu____2198 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2198]  in
                        FStar_List.append scope uu____2189
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2241 =
                      let uu____2244 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2244  in
                    FStar_List.append uu____2241
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2263 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2263 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2289 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2289;
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
                  (let uu____2363 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2363 with
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
                  (let uu____2451 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2451 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2489 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2489 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2489 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2489 FStar_TypeChecker_Common.problem *
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
                          let uu____2557 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2557]  in
                        let uu____2576 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2576
                     in
                  let uu____2579 =
                    let uu____2586 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___359_2597 = wl  in
                       {
                         attempting = (uu___359_2597.attempting);
                         wl_deferred = (uu___359_2597.wl_deferred);
                         ctr = (uu___359_2597.ctr);
                         defer_ok = (uu___359_2597.defer_ok);
                         smt_ok = (uu___359_2597.smt_ok);
                         umax_heuristic_ok =
                           (uu___359_2597.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___359_2597.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2586
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2579 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2615 =
                              let uu____2620 =
                                let uu____2621 =
                                  let uu____2630 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____2630
                                   in
                                [uu____2621]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____2620  in
                            uu____2615 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____2658 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2658;
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
                let uu____2706 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____2706;
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
  'Auu____2721 .
    worklist ->
      'Auu____2721 FStar_TypeChecker_Common.problem ->
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
              let uu____2754 =
                let uu____2757 =
                  let uu____2758 =
                    let uu____2765 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____2765)  in
                  FStar_Syntax_Syntax.NT uu____2758  in
                [uu____2757]  in
              FStar_Syntax_Subst.subst uu____2754 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____2787 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____2787
        then
          let uu____2795 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____2798 = prob_to_string env d  in
          let uu____2800 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____2807 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____2795 uu____2798 uu____2800 uu____2807
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____2819 -> failwith "impossible"  in
           let uu____2822 =
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
           match uu____2822 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_2865  ->
            match uu___15_2865 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____2877 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____2881 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____2881 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_2912  ->
           match uu___16_2912 with
           | UNIV uu____2915 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____2922 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____2922
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
        (fun uu___17_2950  ->
           match uu___17_2950 with
           | UNIV (u',t) ->
               let uu____2955 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____2955
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____2962 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2974 =
        let uu____2975 =
          let uu____2976 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____2976
           in
        FStar_Syntax_Subst.compress uu____2975  in
      FStar_All.pipe_right uu____2974 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____2988 =
        let uu____2989 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____2989  in
      FStar_All.pipe_right uu____2988 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3001 =
        let uu____3005 =
          let uu____3007 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3007  in
        FStar_Pervasives_Native.Some uu____3005  in
      FStar_Profiling.profile (fun uu____3010  -> sn' env t) uu____3001
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
          let uu____3035 =
            let uu____3039 =
              let uu____3041 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3041  in
            FStar_Pervasives_Native.Some uu____3039  in
          FStar_Profiling.profile
            (fun uu____3044  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3035
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3052 = FStar_Syntax_Util.head_and_args t  in
    match uu____3052 with
    | (h,uu____3071) ->
        let uu____3096 =
          let uu____3097 = FStar_Syntax_Subst.compress h  in
          uu____3097.FStar_Syntax_Syntax.n  in
        (match uu____3096 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3102 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3115 =
        let uu____3119 =
          let uu____3121 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3121  in
        FStar_Pervasives_Native.Some uu____3119  in
      FStar_Profiling.profile
        (fun uu____3126  ->
           let uu____3127 = should_strongly_reduce t  in
           if uu____3127
           then
             let uu____3130 =
               let uu____3131 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3131  in
             FStar_All.pipe_right uu____3130 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3115 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3142 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3142) ->
        (FStar_Syntax_Syntax.term * 'Auu____3142)
  =
  fun env  ->
    fun t  ->
      let uu____3165 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3165, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3217  ->
              match uu____3217 with
              | (x,imp) ->
                  let uu____3236 =
                    let uu___465_3237 = x  in
                    let uu____3238 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___465_3237.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___465_3237.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3238
                    }  in
                  (uu____3236, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3262 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3262
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3266 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3266
        | uu____3269 -> u2  in
      let uu____3270 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3270
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3287 =
          let uu____3291 =
            let uu____3293 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3293  in
          FStar_Pervasives_Native.Some uu____3291  in
        FStar_Profiling.profile
          (fun uu____3296  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3287 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3418 = norm_refinement env t12  in
                 match uu____3418 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3433;
                     FStar_Syntax_Syntax.vars = uu____3434;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3458 =
                       let uu____3460 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3462 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3460 uu____3462
                        in
                     failwith uu____3458)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3478 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3478
          | FStar_Syntax_Syntax.Tm_uinst uu____3479 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3516 =
                   let uu____3517 = FStar_Syntax_Subst.compress t1'  in
                   uu____3517.FStar_Syntax_Syntax.n  in
                 match uu____3516 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3532 -> aux true t1'
                 | uu____3540 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3555 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3586 =
                   let uu____3587 = FStar_Syntax_Subst.compress t1'  in
                   uu____3587.FStar_Syntax_Syntax.n  in
                 match uu____3586 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3602 -> aux true t1'
                 | uu____3610 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3625 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3672 =
                   let uu____3673 = FStar_Syntax_Subst.compress t1'  in
                   uu____3673.FStar_Syntax_Syntax.n  in
                 match uu____3672 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3688 -> aux true t1'
                 | uu____3696 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____3711 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____3726 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____3741 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____3756 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____3771 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____3800 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____3833 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____3854 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____3881 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____3909 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____3946 ->
              let uu____3953 =
                let uu____3955 = FStar_Syntax_Print.term_to_string t12  in
                let uu____3957 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____3955 uu____3957
                 in
              failwith uu____3953
          | FStar_Syntax_Syntax.Tm_ascribed uu____3972 ->
              let uu____3999 =
                let uu____4001 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4003 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4001 uu____4003
                 in
              failwith uu____3999
          | FStar_Syntax_Syntax.Tm_delayed uu____4018 ->
              let uu____4033 =
                let uu____4035 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4037 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4035 uu____4037
                 in
              failwith uu____4033
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4052 =
                let uu____4054 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4056 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4054 uu____4056
                 in
              failwith uu____4052
           in
        let uu____4071 = whnf env t1  in aux false uu____4071
  
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
      let uu____4116 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4116 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4157 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4157, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4184 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4184 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4244  ->
    match uu____4244 with
    | (t_base,refopt) ->
        let uu____4275 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4275 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4317 =
      let uu____4321 =
        let uu____4324 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4349  ->
                  match uu____4349 with | (uu____4357,uu____4358,x) -> x))
           in
        FStar_List.append wl.attempting uu____4324  in
      FStar_List.map (wl_prob_to_string wl) uu____4321  in
    FStar_All.pipe_right uu____4317 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____4379 .
    ('Auu____4379 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____4391  ->
    match uu____4391 with
    | (uu____4398,c,args) ->
        let uu____4401 = print_ctx_uvar c  in
        let uu____4403 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4401 uu____4403
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4413 = FStar_Syntax_Util.head_and_args t  in
    match uu____4413 with
    | (head1,_args) ->
        let uu____4457 =
          let uu____4458 = FStar_Syntax_Subst.compress head1  in
          uu____4458.FStar_Syntax_Syntax.n  in
        (match uu____4457 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4462 -> true
         | uu____4476 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4484 = FStar_Syntax_Util.head_and_args t  in
    match uu____4484 with
    | (head1,_args) ->
        let uu____4527 =
          let uu____4528 = FStar_Syntax_Subst.compress head1  in
          uu____4528.FStar_Syntax_Syntax.n  in
        (match uu____4527 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4532) -> u
         | uu____4549 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4574 = FStar_Syntax_Util.head_and_args t  in
      match uu____4574 with
      | (head1,args) ->
          let uu____4621 =
            let uu____4622 = FStar_Syntax_Subst.compress head1  in
            uu____4622.FStar_Syntax_Syntax.n  in
          (match uu____4621 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____4630)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____4663 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_4688  ->
                         match uu___18_4688 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____4693 =
                               let uu____4694 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____4694.FStar_Syntax_Syntax.n  in
                             (match uu____4693 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____4699 -> false)
                         | uu____4701 -> true))
                  in
               (match uu____4663 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____4726 =
                        FStar_List.collect
                          (fun uu___19_4738  ->
                             match uu___19_4738 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____4742 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____4742]
                             | uu____4743 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____4726 FStar_List.rev  in
                    let uu____4766 =
                      let uu____4773 =
                        let uu____4782 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_4804  ->
                                  match uu___20_4804 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____4808 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____4808]
                                  | uu____4809 -> []))
                           in
                        FStar_All.pipe_right uu____4782 FStar_List.rev  in
                      let uu____4832 =
                        let uu____4835 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____4835  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____4773 uu____4832
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____4766 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____4871  ->
                                match uu____4871 with
                                | (x,i) ->
                                    let uu____4890 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____4890, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____4921  ->
                                match uu____4921 with
                                | (a,i) ->
                                    let uu____4940 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____4940, i)) args_sol
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
           | uu____4962 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____4984 =
          let uu____5007 =
            let uu____5008 = FStar_Syntax_Subst.compress k  in
            uu____5008.FStar_Syntax_Syntax.n  in
          match uu____5007 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5090 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5090)
              else
                (let uu____5125 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5125 with
                 | (ys',t1,uu____5158) ->
                     let uu____5163 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5163))
          | uu____5202 ->
              let uu____5203 =
                let uu____5208 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5208)  in
              ((ys, t), uu____5203)
           in
        match uu____4984 with
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
                 let uu____5303 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5303 c  in
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
               (let uu____5381 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5381
                then
                  let uu____5386 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5388 = print_ctx_uvar uv  in
                  let uu____5390 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5386 uu____5388 uu____5390
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5399 =
                   let uu____5401 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5401  in
                 let uu____5404 =
                   let uu____5407 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5407
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5399 uu____5404 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5440 =
               let uu____5441 =
                 let uu____5443 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5445 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5443 uu____5445
                  in
               failwith uu____5441  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5511  ->
                       match uu____5511 with
                       | (a,i) ->
                           let uu____5532 =
                             let uu____5533 = FStar_Syntax_Subst.compress a
                                in
                             uu____5533.FStar_Syntax_Syntax.n  in
                           (match uu____5532 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5559 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5569 =
                 let uu____5571 = is_flex g  in Prims.op_Negation uu____5571
                  in
               if uu____5569
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____5580 = destruct_flex_t g wl  in
                  match uu____5580 with
                  | ((uu____5585,uv1,args),wl1) ->
                      ((let uu____5590 = args_as_binders args  in
                        assign_solution uu____5590 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___718_5592 = wl1  in
              {
                attempting = (uu___718_5592.attempting);
                wl_deferred = (uu___718_5592.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___718_5592.defer_ok);
                smt_ok = (uu___718_5592.smt_ok);
                umax_heuristic_ok = (uu___718_5592.umax_heuristic_ok);
                tcenv = (uu___718_5592.tcenv);
                wl_implicits = (uu___718_5592.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____5617 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____5617
         then
           let uu____5622 = FStar_Util.string_of_int pid  in
           let uu____5624 =
             let uu____5626 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____5626 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5622 uu____5624
         else ());
        commit sol;
        (let uu___726_5640 = wl  in
         {
           attempting = (uu___726_5640.attempting);
           wl_deferred = (uu___726_5640.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___726_5640.defer_ok);
           smt_ok = (uu___726_5640.smt_ok);
           umax_heuristic_ok = (uu___726_5640.umax_heuristic_ok);
           tcenv = (uu___726_5640.tcenv);
           wl_implicits = (uu___726_5640.wl_implicits)
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
          (let uu____5676 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____5676
           then
             let uu____5681 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____5685 =
               let uu____5687 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____5687 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____5681 uu____5685
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
        let uu____5722 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____5722 FStar_Util.set_elements  in
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
      let uu____5762 = occurs uk t  in
      match uu____5762 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____5801 =
                 let uu____5803 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____5805 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____5803 uu____5805
                  in
               FStar_Pervasives_Native.Some uu____5801)
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
            let uu____5925 = maximal_prefix bs_tail bs'_tail  in
            (match uu____5925 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____5976 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6033  ->
             match uu____6033 with
             | (x,uu____6045) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6063 = FStar_List.last bs  in
      match uu____6063 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6087) ->
          let uu____6098 =
            FStar_Util.prefix_until
              (fun uu___21_6113  ->
                 match uu___21_6113 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6116 -> false) g
             in
          (match uu____6098 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6130,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6167 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6167 with
        | (pfx,uu____6177) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6189 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6189 with
             | (uu____6197,src',wl1) ->
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
                 | uu____6311 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6312 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6376  ->
                  fun uu____6377  ->
                    match (uu____6376, uu____6377) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6480 =
                          let uu____6482 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6482
                           in
                        if uu____6480
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6516 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6516
                           then
                             let uu____6533 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6533)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6312 with | (isect,uu____6583) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____6619 'Auu____6620 .
    (FStar_Syntax_Syntax.bv * 'Auu____6619) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____6620) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____6678  ->
              fun uu____6679  ->
                match (uu____6678, uu____6679) with
                | ((a,uu____6698),(b,uu____6700)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____6716 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____6716) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____6747  ->
           match uu____6747 with
           | (y,uu____6754) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____6764 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____6764) Prims.list ->
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
                   let uu____6926 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____6926
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____6959 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7011 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7055 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7076 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7084  ->
    match uu___22_7084 with
    | MisMatch (d1,d2) ->
        let uu____7096 =
          let uu____7098 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7100 =
            let uu____7102 =
              let uu____7104 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7104 ")"  in
            Prims.op_Hat ") (" uu____7102  in
          Prims.op_Hat uu____7098 uu____7100  in
        Prims.op_Hat "MisMatch (" uu____7096
    | HeadMatch u ->
        let uu____7111 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7111
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7120  ->
    match uu___23_7120 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7137 -> HeadMatch false
  
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
          let uu____7159 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7159 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7170 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7194 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7204 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7223 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7223
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7224 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7225 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7226 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7239 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7253 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7277) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7283,uu____7284) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7326) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7351;
             FStar_Syntax_Syntax.index = uu____7352;
             FStar_Syntax_Syntax.sort = t2;_},uu____7354)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7362 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7363 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7364 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7379 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7386 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7406 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7406
  
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
           { FStar_Syntax_Syntax.blob = uu____7425;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7426;
             FStar_Syntax_Syntax.ltyp = uu____7427;
             FStar_Syntax_Syntax.rng = uu____7428;_},uu____7429)
            ->
            let uu____7440 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7440 t21
        | (uu____7441,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7442;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7443;
             FStar_Syntax_Syntax.ltyp = uu____7444;
             FStar_Syntax_Syntax.rng = uu____7445;_})
            ->
            let uu____7456 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7456
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7468 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7468
            then FullMatch
            else
              (let uu____7473 =
                 let uu____7482 =
                   let uu____7485 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7485  in
                 let uu____7486 =
                   let uu____7489 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7489  in
                 (uu____7482, uu____7486)  in
               MisMatch uu____7473)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7495),FStar_Syntax_Syntax.Tm_uinst (g,uu____7497)) ->
            let uu____7506 = head_matches env f g  in
            FStar_All.pipe_right uu____7506 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7507) -> HeadMatch true
        | (uu____7509,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7513 = FStar_Const.eq_const c d  in
            if uu____7513
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7523),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7525)) ->
            let uu____7558 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7558
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7568),FStar_Syntax_Syntax.Tm_refine (y,uu____7570)) ->
            let uu____7579 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7579 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____7581),uu____7582) ->
            let uu____7587 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____7587 head_match
        | (uu____7588,FStar_Syntax_Syntax.Tm_refine (x,uu____7590)) ->
            let uu____7595 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____7595 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7596,FStar_Syntax_Syntax.Tm_type
           uu____7597) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____7599,FStar_Syntax_Syntax.Tm_arrow uu____7600) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____7631),FStar_Syntax_Syntax.Tm_app (head',uu____7633))
            ->
            let uu____7682 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____7682 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____7684),uu____7685) ->
            let uu____7710 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____7710 head_match
        | (uu____7711,FStar_Syntax_Syntax.Tm_app (head1,uu____7713)) ->
            let uu____7738 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____7738 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____7739,FStar_Syntax_Syntax.Tm_let
           uu____7740) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____7768,FStar_Syntax_Syntax.Tm_match uu____7769) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____7815,FStar_Syntax_Syntax.Tm_abs
           uu____7816) -> HeadMatch true
        | uu____7854 ->
            let uu____7859 =
              let uu____7868 = delta_depth_of_term env t11  in
              let uu____7871 = delta_depth_of_term env t21  in
              (uu____7868, uu____7871)  in
            MisMatch uu____7859
  
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
              let uu____7940 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____7940  in
            (let uu____7942 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____7942
             then
               let uu____7947 = FStar_Syntax_Print.term_to_string t  in
               let uu____7949 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____7947 uu____7949
             else ());
            (let uu____7954 =
               let uu____7955 = FStar_Syntax_Util.un_uinst head1  in
               uu____7955.FStar_Syntax_Syntax.n  in
             match uu____7954 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____7961 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____7961 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____7975 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____7975
                        then
                          let uu____7980 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____7980
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____7985 ->
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
                      let uu____8003 =
                        let uu____8005 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8005 = FStar_Syntax_Util.Equal  in
                      if uu____8003
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8012 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8012
                          then
                            let uu____8017 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8019 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8017
                              uu____8019
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8024 -> FStar_Pervasives_Native.None)
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
            (let uu____8176 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8176
             then
               let uu____8181 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8183 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8185 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8181
                 uu____8183 uu____8185
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8213 =
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
               match uu____8213 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8261 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8261 with
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
                  uu____8299),uu____8300)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8321 =
                      let uu____8330 = maybe_inline t11  in
                      let uu____8333 = maybe_inline t21  in
                      (uu____8330, uu____8333)  in
                    match uu____8321 with
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
                 (uu____8376,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8377))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8398 =
                      let uu____8407 = maybe_inline t11  in
                      let uu____8410 = maybe_inline t21  in
                      (uu____8407, uu____8410)  in
                    match uu____8398 with
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
             | MisMatch uu____8465 -> fail1 n_delta r t11 t21
             | uu____8474 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8489 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8489
           then
             let uu____8494 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8496 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8498 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8506 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8523 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8523
                    (fun uu____8558  ->
                       match uu____8558 with
                       | (t11,t21) ->
                           let uu____8566 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8568 =
                             let uu____8570 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8570  in
                           Prims.op_Hat uu____8566 uu____8568))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8494 uu____8496 uu____8498 uu____8506
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____8587 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____8587 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_8602  ->
    match uu___24_8602 with
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
      let uu___1215_8651 = p  in
      let uu____8654 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____8655 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1215_8651.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____8654;
        FStar_TypeChecker_Common.relation =
          (uu___1215_8651.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____8655;
        FStar_TypeChecker_Common.element =
          (uu___1215_8651.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1215_8651.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1215_8651.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1215_8651.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1215_8651.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1215_8651.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____8670 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____8670
            (fun _8675  -> FStar_TypeChecker_Common.TProb _8675)
      | FStar_TypeChecker_Common.CProb uu____8676 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____8699 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____8699 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____8707 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____8707 with
           | (lh,lhs_args) ->
               let uu____8754 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____8754 with
                | (rh,rhs_args) ->
                    let uu____8801 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8814,FStar_Syntax_Syntax.Tm_uvar uu____8815)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____8904 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____8931,uu____8932)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____8947,FStar_Syntax_Syntax.Tm_uvar uu____8948)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8963,FStar_Syntax_Syntax.Tm_arrow uu____8964)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_8994 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_8994.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_8994.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_8994.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_8994.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_8994.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_8994.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_8994.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_8994.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_8994.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____8997,FStar_Syntax_Syntax.Tm_type uu____8998)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_9014 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_9014.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_9014.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_9014.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_9014.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_9014.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_9014.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_9014.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_9014.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_9014.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9017,FStar_Syntax_Syntax.Tm_uvar uu____9018)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1266_9034 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1266_9034.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1266_9034.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1266_9034.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1266_9034.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1266_9034.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1266_9034.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1266_9034.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1266_9034.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1266_9034.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9037,FStar_Syntax_Syntax.Tm_uvar uu____9038)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9053,uu____9054)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9069,FStar_Syntax_Syntax.Tm_uvar uu____9070)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9085,uu____9086) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____8801 with
                     | (rank,tp1) ->
                         let uu____9099 =
                           FStar_All.pipe_right
                             (let uu___1286_9103 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1286_9103.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1286_9103.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1286_9103.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1286_9103.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1286_9103.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1286_9103.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1286_9103.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1286_9103.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1286_9103.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9106  ->
                                FStar_TypeChecker_Common.TProb _9106)
                            in
                         (rank, uu____9099))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9110 =
            FStar_All.pipe_right
              (let uu___1290_9114 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1290_9114.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1290_9114.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1290_9114.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1290_9114.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1290_9114.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1290_9114.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1290_9114.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1290_9114.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1290_9114.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9117  -> FStar_TypeChecker_Common.CProb _9117)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9110)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9177 probs =
      match uu____9177 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9258 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9279 = rank wl.tcenv hd1  in
               (match uu____9279 with
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
                      (let uu____9340 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9345 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9345)
                          in
                       if uu____9340
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
          let uu____9418 = FStar_Syntax_Util.head_and_args t  in
          match uu____9418 with
          | (hd1,uu____9437) ->
              let uu____9462 =
                let uu____9463 = FStar_Syntax_Subst.compress hd1  in
                uu____9463.FStar_Syntax_Syntax.n  in
              (match uu____9462 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9468) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9503  ->
                           match uu____9503 with
                           | (y,uu____9512) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9535  ->
                                       match uu____9535 with
                                       | (x,uu____9544) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9549 -> false)
           in
        let uu____9551 = rank tcenv p  in
        match uu____9551 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9560 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9641 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____9660 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____9679 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____9696 = FStar_Thunk.mkv s  in UFailed uu____9696 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____9711 = mklstr s  in UFailed uu____9711 
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
                        let uu____9762 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____9762 with
                        | (k,uu____9770) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____9783 -> false)))
            | uu____9785 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____9837 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____9845 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____9845 = Prims.int_zero))
                           in
                        if uu____9837 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____9866 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____9874 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____9874 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____9866)
               in
            let uu____9878 = filter1 u12  in
            let uu____9881 = filter1 u22  in (uu____9878, uu____9881)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____9916 = filter_out_common_univs us1 us2  in
                   (match uu____9916 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____9976 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____9976 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____9979 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____9996  ->
                               let uu____9997 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____9999 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____9997 uu____9999))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10025 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10025 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10051 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10051 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10054 ->
                   ufailed_thunk
                     (fun uu____10065  ->
                        let uu____10066 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10068 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10066 uu____10068 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10071,uu____10072) ->
              let uu____10074 =
                let uu____10076 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10078 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10076 uu____10078
                 in
              failwith uu____10074
          | (FStar_Syntax_Syntax.U_unknown ,uu____10081) ->
              let uu____10082 =
                let uu____10084 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10086 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10084 uu____10086
                 in
              failwith uu____10082
          | (uu____10089,FStar_Syntax_Syntax.U_bvar uu____10090) ->
              let uu____10092 =
                let uu____10094 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10096 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10094 uu____10096
                 in
              failwith uu____10092
          | (uu____10099,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10100 =
                let uu____10102 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10104 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10102 uu____10104
                 in
              failwith uu____10100
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10134 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10134
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10151 = occurs_univ v1 u3  in
              if uu____10151
              then
                let uu____10154 =
                  let uu____10156 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10158 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10156 uu____10158
                   in
                try_umax_components u11 u21 uu____10154
              else
                (let uu____10163 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10163)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10175 = occurs_univ v1 u3  in
              if uu____10175
              then
                let uu____10178 =
                  let uu____10180 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10182 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10180 uu____10182
                   in
                try_umax_components u11 u21 uu____10178
              else
                (let uu____10187 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10187)
          | (FStar_Syntax_Syntax.U_max uu____10188,uu____10189) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10197 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10197
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10203,FStar_Syntax_Syntax.U_max uu____10204) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10212 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10212
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10218,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10220,FStar_Syntax_Syntax.U_name uu____10221) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10223) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10225) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10227,FStar_Syntax_Syntax.U_succ uu____10228) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10230,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10337 = bc1  in
      match uu____10337 with
      | (bs1,mk_cod1) ->
          let uu____10381 = bc2  in
          (match uu____10381 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10492 = aux xs ys  in
                     (match uu____10492 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10575 =
                       let uu____10582 = mk_cod1 xs  in ([], uu____10582)  in
                     let uu____10585 =
                       let uu____10592 = mk_cod2 ys  in ([], uu____10592)  in
                     (uu____10575, uu____10585)
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
                  let uu____10661 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____10661 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____10664 =
                    let uu____10665 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____10665 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____10664
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____10670 = has_type_guard t1 t2  in (uu____10670, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____10671 = has_type_guard t2 t1  in (uu____10671, wl)
  
let is_flex_pat :
  'Auu____10681 'Auu____10682 'Auu____10683 .
    ('Auu____10681 * 'Auu____10682 * 'Auu____10683 Prims.list) -> Prims.bool
  =
  fun uu___25_10697  ->
    match uu___25_10697 with
    | (uu____10706,uu____10707,[]) -> true
    | uu____10711 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____10744 = f  in
      match uu____10744 with
      | (uu____10751,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____10752;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____10753;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____10756;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____10757;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____10758;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____10759;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____10829  ->
                 match uu____10829 with
                 | (y,uu____10838) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____10992 =
                  let uu____11007 =
                    let uu____11010 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11010  in
                  ((FStar_List.rev pat_binders), uu____11007)  in
                FStar_Pervasives_Native.Some uu____10992
            | (uu____11043,[]) ->
                let uu____11074 =
                  let uu____11089 =
                    let uu____11092 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11092  in
                  ((FStar_List.rev pat_binders), uu____11089)  in
                FStar_Pervasives_Native.Some uu____11074
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11183 =
                  let uu____11184 = FStar_Syntax_Subst.compress a  in
                  uu____11184.FStar_Syntax_Syntax.n  in
                (match uu____11183 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11204 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11204
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1618_11234 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1618_11234.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1618_11234.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11238 =
                            let uu____11239 =
                              let uu____11246 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11246)  in
                            FStar_Syntax_Syntax.NT uu____11239  in
                          [uu____11238]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1624_11262 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1624_11262.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1624_11262.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11263 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11303 =
                  let uu____11310 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11310  in
                (match uu____11303 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11369 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11394 ->
               let uu____11395 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11395 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____11691 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____11691
       then
         let uu____11696 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____11696
       else ());
      (let uu____11702 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____11702
       then
         let uu____11707 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____11707
       else ());
      (let uu____11712 = next_prob probs  in
       match uu____11712 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1651_11739 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1651_11739.wl_deferred);
               ctr = (uu___1651_11739.ctr);
               defer_ok = (uu___1651_11739.defer_ok);
               smt_ok = (uu___1651_11739.smt_ok);
               umax_heuristic_ok = (uu___1651_11739.umax_heuristic_ok);
               tcenv = (uu___1651_11739.tcenv);
               wl_implicits = (uu___1651_11739.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____11748 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____11748
                 then
                   let uu____11751 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____11751
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
                       (let uu____11758 =
                          defer_lit
                            "deferring flex_rigid or flex_flex subtyping" hd1
                            probs1
                           in
                        solve env uu____11758)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1663_11764 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1663_11764.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1663_11764.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1663_11764.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1663_11764.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1663_11764.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1663_11764.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1663_11764.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1663_11764.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1663_11764.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____11789 ->
                let uu____11799 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____11864  ->
                          match uu____11864 with
                          | (c,uu____11874,uu____11875) -> c < probs.ctr))
                   in
                (match uu____11799 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____11923 =
                            let uu____11928 =
                              FStar_List.map
                                (fun uu____11949  ->
                                   match uu____11949 with
                                   | (uu____11965,x,y) ->
                                       let uu____11976 = FStar_Thunk.force x
                                          in
                                       (uu____11976, y)) probs.wl_deferred
                               in
                            (uu____11928, (probs.wl_implicits))  in
                          Success uu____11923
                      | uu____11980 ->
                          let uu____11990 =
                            let uu___1681_11991 = probs  in
                            let uu____11992 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12013  ->
                                      match uu____12013 with
                                      | (uu____12021,uu____12022,y) -> y))
                               in
                            {
                              attempting = uu____11992;
                              wl_deferred = rest;
                              ctr = (uu___1681_11991.ctr);
                              defer_ok = (uu___1681_11991.defer_ok);
                              smt_ok = (uu___1681_11991.smt_ok);
                              umax_heuristic_ok =
                                (uu___1681_11991.umax_heuristic_ok);
                              tcenv = (uu___1681_11991.tcenv);
                              wl_implicits = (uu___1681_11991.wl_implicits)
                            }  in
                          solve env uu____11990))))

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
            let uu____12031 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12031 with
            | USolved wl1 ->
                let uu____12033 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12033
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12036 = defer_lit "" orig wl1  in
                solve env uu____12036

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
                  let uu____12087 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12087 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12090 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12103;
                  FStar_Syntax_Syntax.vars = uu____12104;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12107;
                  FStar_Syntax_Syntax.vars = uu____12108;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12121,uu____12122) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12130,FStar_Syntax_Syntax.Tm_uinst uu____12131) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12139 -> USolved wl

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
            ((let uu____12150 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12150
              then
                let uu____12155 = prob_to_string env orig  in
                let uu____12157 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12155 uu____12157
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
               let uu____12250 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12250 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12305 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12305
                then
                  let uu____12310 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12312 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12310 uu____12312
                else ());
               (let uu____12317 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12317 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12363 = eq_prob t1 t2 wl2  in
                         (match uu____12363 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12384 ->
                         let uu____12393 = eq_prob t1 t2 wl2  in
                         (match uu____12393 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____12443 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____12458 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____12459 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____12458, uu____12459)
                           | FStar_Pervasives_Native.None  ->
                               let uu____12464 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____12465 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____12464, uu____12465)
                            in
                         (match uu____12443 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____12496 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____12496 with
                                | (t1_hd,t1_args) ->
                                    let uu____12541 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____12541 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____12607 =
                                              let uu____12614 =
                                                let uu____12625 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____12625 :: t1_args  in
                                              let uu____12642 =
                                                let uu____12651 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____12651 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____12700  ->
                                                   fun uu____12701  ->
                                                     fun uu____12702  ->
                                                       match (uu____12700,
                                                               uu____12701,
                                                               uu____12702)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____12752),
                                                          (a2,uu____12754))
                                                           ->
                                                           let uu____12791 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____12791
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____12614
                                                uu____12642
                                               in
                                            match uu____12607 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1835_12817 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1835_12817.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1835_12817.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1835_12817.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____12828 =
                                                  solve env1 wl'  in
                                                (match uu____12828 with
                                                 | Success (uu____12831,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1844_12835
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1844_12835.attempting);
                                                            wl_deferred =
                                                              (uu___1844_12835.wl_deferred);
                                                            ctr =
                                                              (uu___1844_12835.ctr);
                                                            defer_ok =
                                                              (uu___1844_12835.defer_ok);
                                                            smt_ok =
                                                              (uu___1844_12835.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1844_12835.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1844_12835.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____12836 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____12868 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____12868 with
                                | (t1_base,p1_opt) ->
                                    let uu____12904 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____12904 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13003 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13003
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
                                               let uu____13056 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13056
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
                                               let uu____13088 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13088
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
                                               let uu____13120 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13120
                                           | uu____13123 -> t_base  in
                                         let uu____13140 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13140 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13154 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13154, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13161 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13161 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13197 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13197 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13233 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13233
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
                              let uu____13257 = combine t11 t21 wl2  in
                              (match uu____13257 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13290 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13290
                                     then
                                       let uu____13295 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13295
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13337 ts1 =
               match uu____13337 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13400 = pairwise out t wl2  in
                        (match uu____13400 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____13436 =
               let uu____13447 = FStar_List.hd ts  in (uu____13447, [], wl1)
                in
             let uu____13456 = FStar_List.tl ts  in
             aux uu____13436 uu____13456  in
           let uu____13463 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____13463 with
           | (this_flex,this_rigid) ->
               let uu____13489 =
                 let uu____13490 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____13490.FStar_Syntax_Syntax.n  in
               (match uu____13489 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____13515 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____13515
                    then
                      let uu____13518 = destruct_flex_t this_flex wl  in
                      (match uu____13518 with
                       | (flex,wl1) ->
                           let uu____13525 = quasi_pattern env flex  in
                           (match uu____13525 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____13544 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____13544
                                  then
                                    let uu____13549 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____13549
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____13556 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___1946_13559 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___1946_13559.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___1946_13559.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___1946_13559.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___1946_13559.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___1946_13559.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___1946_13559.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___1946_13559.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___1946_13559.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___1946_13559.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____13556)
                | uu____13560 ->
                    ((let uu____13562 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____13562
                      then
                        let uu____13567 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____13567
                      else ());
                     (let uu____13572 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____13572 with
                      | (u,_args) ->
                          let uu____13615 =
                            let uu____13616 = FStar_Syntax_Subst.compress u
                               in
                            uu____13616.FStar_Syntax_Syntax.n  in
                          (match uu____13615 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____13644 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____13644 with
                                 | (u',uu____13663) ->
                                     let uu____13688 =
                                       let uu____13689 = whnf env u'  in
                                       uu____13689.FStar_Syntax_Syntax.n  in
                                     (match uu____13688 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____13711 -> false)
                                  in
                               let uu____13713 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_13736  ->
                                         match uu___26_13736 with
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
                                              | uu____13750 -> false)
                                         | uu____13754 -> false))
                                  in
                               (match uu____13713 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____13769 = whnf env this_rigid
                                         in
                                      let uu____13770 =
                                        FStar_List.collect
                                          (fun uu___27_13776  ->
                                             match uu___27_13776 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____13782 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____13782]
                                             | uu____13786 -> [])
                                          bounds_probs
                                         in
                                      uu____13769 :: uu____13770  in
                                    let uu____13787 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____13787 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____13820 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____13835 =
                                               let uu____13836 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____13836.FStar_Syntax_Syntax.n
                                                in
                                             match uu____13835 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____13848 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____13848)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____13859 -> bound  in
                                           let uu____13860 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____13860)  in
                                         (match uu____13820 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____13895 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____13895
                                                then
                                                  let wl'1 =
                                                    let uu___2006_13901 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2006_13901.wl_deferred);
                                                      ctr =
                                                        (uu___2006_13901.ctr);
                                                      defer_ok =
                                                        (uu___2006_13901.defer_ok);
                                                      smt_ok =
                                                        (uu___2006_13901.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2006_13901.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2006_13901.tcenv);
                                                      wl_implicits =
                                                        (uu___2006_13901.wl_implicits)
                                                    }  in
                                                  let uu____13902 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____13902
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13908 =
                                                  solve_t env eq_prob
                                                    (let uu___2011_13910 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2011_13910.wl_deferred);
                                                       ctr =
                                                         (uu___2011_13910.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2011_13910.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2011_13910.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2011_13910.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____13908 with
                                                | Success (uu____13912,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2017_13915 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2017_13915.wl_deferred);
                                                        ctr =
                                                          (uu___2017_13915.ctr);
                                                        defer_ok =
                                                          (uu___2017_13915.defer_ok);
                                                        smt_ok =
                                                          (uu___2017_13915.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2017_13915.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2017_13915.tcenv);
                                                        wl_implicits =
                                                          (uu___2017_13915.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2020_13917 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2020_13917.attempting);
                                                        wl_deferred =
                                                          (uu___2020_13917.wl_deferred);
                                                        ctr =
                                                          (uu___2020_13917.ctr);
                                                        defer_ok =
                                                          (uu___2020_13917.defer_ok);
                                                        smt_ok =
                                                          (uu___2020_13917.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2020_13917.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2020_13917.tcenv);
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
                                                    let uu____13933 =
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
                                                    ((let uu____13945 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____13945
                                                      then
                                                        let uu____13950 =
                                                          let uu____13952 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____13952
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____13950
                                                      else ());
                                                     (let uu____13965 =
                                                        let uu____13980 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____13980)
                                                         in
                                                      match uu____13965 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14002))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14028 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14028
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
                                                                  let uu____14048
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14048))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14073 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14073
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
                                                                    let uu____14093
                                                                    =
                                                                    let uu____14098
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14098
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14093
                                                                    [] wl2
                                                                     in
                                                                  let uu____14104
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14104))))
                                                      | uu____14105 ->
                                                          let uu____14120 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14120 p)))))))
                           | uu____14127 when flip ->
                               let uu____14128 =
                                 let uu____14130 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14132 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14130 uu____14132
                                  in
                               failwith uu____14128
                           | uu____14135 ->
                               let uu____14136 =
                                 let uu____14138 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14140 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14138 uu____14140
                                  in
                               failwith uu____14136)))))

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
                      (fun uu____14176  ->
                         match uu____14176 with
                         | (x,i) ->
                             let uu____14195 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14195, i)) bs_lhs
                     in
                  let uu____14198 = lhs  in
                  match uu____14198 with
                  | (uu____14199,u_lhs,uu____14201) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14298 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14308 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14308, univ)
                             in
                          match uu____14298 with
                          | (k,univ) ->
                              let uu____14315 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14315 with
                               | (uu____14332,u,wl3) ->
                                   let uu____14335 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14335, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14361 =
                              let uu____14374 =
                                let uu____14385 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14385 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____14436  ->
                                   fun uu____14437  ->
                                     match (uu____14436, uu____14437) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____14538 =
                                           let uu____14545 =
                                             let uu____14548 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____14548
                                              in
                                           copy_uvar u_lhs [] uu____14545 wl2
                                            in
                                         (match uu____14538 with
                                          | (uu____14577,t_a,wl3) ->
                                              let uu____14580 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____14580 with
                                               | (uu____14599,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14374
                                ([], wl1)
                               in
                            (match uu____14361 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2131_14655 = ct  in
                                   let uu____14656 =
                                     let uu____14659 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____14659
                                      in
                                   let uu____14674 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2131_14655.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2131_14655.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____14656;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____14674;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2131_14655.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2134_14692 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2134_14692.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2134_14692.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____14695 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____14695 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____14733 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____14733 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____14744 =
                                          let uu____14749 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____14749)  in
                                        TERM uu____14744  in
                                      let uu____14750 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____14750 with
                                       | (sub_prob,wl3) ->
                                           let uu____14764 =
                                             let uu____14765 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____14765
                                              in
                                           solve env uu____14764))
                             | (x,imp)::formals2 ->
                                 let uu____14787 =
                                   let uu____14794 =
                                     let uu____14797 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____14797
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____14794 wl1
                                    in
                                 (match uu____14787 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____14818 =
                                          let uu____14821 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____14821
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____14818 u_x
                                         in
                                      let uu____14822 =
                                        let uu____14825 =
                                          let uu____14828 =
                                            let uu____14829 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____14829, imp)  in
                                          [uu____14828]  in
                                        FStar_List.append bs_terms
                                          uu____14825
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____14822 formals2 wl2)
                              in
                           let uu____14856 = occurs_check u_lhs arrow1  in
                           (match uu____14856 with
                            | (uu____14869,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____14885 =
                                    mklstr
                                      (fun uu____14890  ->
                                         let uu____14891 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____14891)
                                     in
                                  giveup_or_defer env orig wl uu____14885
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
              (let uu____14924 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____14924
               then
                 let uu____14929 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____14932 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____14929 (rel_to_string (p_rel orig)) uu____14932
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15063 = rhs wl1 scope env1 subst1  in
                     (match uu____15063 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15086 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15086
                            then
                              let uu____15091 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15091
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15169 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15169 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2204_15171 = hd1  in
                       let uu____15172 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2204_15171.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2204_15171.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15172
                       }  in
                     let hd21 =
                       let uu___2207_15176 = hd2  in
                       let uu____15177 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2207_15176.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2207_15176.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15177
                       }  in
                     let uu____15180 =
                       let uu____15185 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15185
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15180 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15208 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15208
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15215 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15215 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15287 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15287
                                  in
                               ((let uu____15305 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15305
                                 then
                                   let uu____15310 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15312 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15310
                                     uu____15312
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15347 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15383 = aux wl [] env [] bs1 bs2  in
               match uu____15383 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____15442 = attempt sub_probs wl2  in
                   solve env1 uu____15442)

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
            let uu___2245_15462 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2245_15462.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2245_15462.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____15474 = try_solve env wl'  in
          match uu____15474 with
          | Success (uu____15475,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2254_15479 = wl  in
                  {
                    attempting = (uu___2254_15479.attempting);
                    wl_deferred = (uu___2254_15479.wl_deferred);
                    ctr = (uu___2254_15479.ctr);
                    defer_ok = (uu___2254_15479.defer_ok);
                    smt_ok = (uu___2254_15479.smt_ok);
                    umax_heuristic_ok = (uu___2254_15479.umax_heuristic_ok);
                    tcenv = (uu___2254_15479.tcenv);
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
        (let uu____15488 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____15488 wl)

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
              let uu____15502 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____15502 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____15536 = lhs1  in
              match uu____15536 with
              | (uu____15539,ctx_u,uu____15541) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____15549 ->
                        let uu____15550 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____15550 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____15599 = quasi_pattern env1 lhs1  in
              match uu____15599 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____15633) ->
                  let uu____15638 = lhs1  in
                  (match uu____15638 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____15653 = occurs_check ctx_u rhs1  in
                       (match uu____15653 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____15704 =
                                let uu____15712 =
                                  let uu____15714 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____15714
                                   in
                                FStar_Util.Inl uu____15712  in
                              (uu____15704, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____15742 =
                                 let uu____15744 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____15744  in
                               if uu____15742
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____15771 =
                                    let uu____15779 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____15779  in
                                  let uu____15785 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____15771, uu____15785)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____15829 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____15829 with
              | (rhs_hd,args) ->
                  let uu____15872 = FStar_Util.prefix args  in
                  (match uu____15872 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____15944 = lhs1  in
                       (match uu____15944 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____15948 =
                              let uu____15959 =
                                let uu____15966 =
                                  let uu____15969 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____15969
                                   in
                                copy_uvar u_lhs [] uu____15966 wl1  in
                              match uu____15959 with
                              | (uu____15996,t_last_arg,wl2) ->
                                  let uu____15999 =
                                    let uu____16006 =
                                      let uu____16007 =
                                        let uu____16016 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____16016]  in
                                      FStar_List.append bs_lhs uu____16007
                                       in
                                    copy_uvar u_lhs uu____16006 t_res_lhs wl2
                                     in
                                  (match uu____15999 with
                                   | (uu____16051,lhs',wl3) ->
                                       let uu____16054 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____16054 with
                                        | (uu____16071,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____15948 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____16092 =
                                     let uu____16093 =
                                       let uu____16098 =
                                         let uu____16099 =
                                           let uu____16102 =
                                             let uu____16107 =
                                               let uu____16108 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____16108]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____16107
                                              in
                                           uu____16102
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____16099
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____16098)  in
                                     TERM uu____16093  in
                                   [uu____16092]  in
                                 let uu____16133 =
                                   let uu____16140 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____16140 with
                                   | (p1,wl3) ->
                                       let uu____16160 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____16160 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____16133 with
                                  | (sub_probs,wl3) ->
                                      let uu____16192 =
                                        let uu____16193 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____16193  in
                                      solve env1 uu____16192))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____16227 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____16227 with
                | (uu____16245,args) ->
                    (match args with | [] -> false | uu____16281 -> true)
                 in
              let is_arrow rhs2 =
                let uu____16300 =
                  let uu____16301 = FStar_Syntax_Subst.compress rhs2  in
                  uu____16301.FStar_Syntax_Syntax.n  in
                match uu____16300 with
                | FStar_Syntax_Syntax.Tm_arrow uu____16305 -> true
                | uu____16321 -> false  in
              let uu____16323 = quasi_pattern env1 lhs1  in
              match uu____16323 with
              | FStar_Pervasives_Native.None  ->
                  let msg =
                    mklstr
                      (fun uu____16342  ->
                         let uu____16343 = prob_to_string env1 orig1  in
                         FStar_Util.format1
                           "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                           uu____16343)
                     in
                  giveup_or_defer env1 orig1 wl1 msg
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____16352 = is_app rhs1  in
                  if uu____16352
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____16357 = is_arrow rhs1  in
                     if uu____16357
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let msg =
                          mklstr
                            (fun uu____16370  ->
                               let uu____16371 = prob_to_string env1 orig1
                                  in
                               FStar_Util.format1
                                 "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                 uu____16371)
                           in
                        giveup_or_defer env1 orig1 wl1 msg))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____16375 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16375
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16381 = FStar_Thunk.mkv "flex-rigid subtyping"
                     in
                  giveup_or_defer env orig wl uu____16381
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____16386 = lhs  in
                (match uu____16386 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____16390 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____16390 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____16408 =
                              let uu____16412 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____16412
                               in
                            FStar_All.pipe_right uu____16408
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____16433 = occurs_check ctx_uv rhs1  in
                          (match uu____16433 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16462 =
                                   let uu____16463 =
                                     let uu____16465 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat "occurs-check failed: "
                                       uu____16465
                                      in
                                   FStar_All.pipe_left FStar_Thunk.mkv
                                     uu____16463
                                    in
                                 giveup_or_defer env orig wl uu____16462
                               else
                                 (let uu____16473 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____16473
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____16480 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____16480
                                  else
                                    if wl.defer_ok
                                    then
                                      (let msg1 =
                                         mklstr
                                           (fun uu____16496  ->
                                              let uu____16497 =
                                                names_to_string1 fvs2  in
                                              let uu____16499 =
                                                names_to_string1 fvs1  in
                                              let uu____16501 =
                                                FStar_Syntax_Print.binders_to_string
                                                  ", "
                                                  (FStar_List.append
                                                     ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                     lhs_binders)
                                                 in
                                              FStar_Util.format3
                                                "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                uu____16497 uu____16499
                                                uu____16501)
                                          in
                                       giveup_or_defer env orig wl msg1)
                                    else first_order orig env wl lhs rhs1))
                      | uu____16513 ->
                          if wl.defer_ok
                          then
                            let uu____16517 = FStar_Thunk.mkv "Not a pattern"
                               in
                            giveup_or_defer env orig wl uu____16517
                          else
                            (let uu____16522 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____16522 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____16548 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____16548
                             | (FStar_Util.Inl msg,uu____16550) ->
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
                  let uu____16568 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16568
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____16574 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____16574
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then
                  let uu____16596 = FStar_Thunk.mkv "flex-flex non-pattern"
                     in
                  giveup_or_defer env orig wl uu____16596
                else
                  (let uu____16601 =
                     let uu____16618 = quasi_pattern env lhs  in
                     let uu____16625 = quasi_pattern env rhs  in
                     (uu____16618, uu____16625)  in
                   match uu____16601 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____16668 = lhs  in
                       (match uu____16668 with
                        | ({ FStar_Syntax_Syntax.n = uu____16669;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____16671;_},u_lhs,uu____16673)
                            ->
                            let uu____16676 = rhs  in
                            (match uu____16676 with
                             | (uu____16677,u_rhs,uu____16679) ->
                                 let uu____16680 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____16680
                                 then
                                   let uu____16687 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____16687
                                 else
                                   (let uu____16690 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____16690 with
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
                                        let uu____16722 =
                                          let uu____16729 =
                                            let uu____16732 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____16732
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____16729
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____16722 with
                                         | (uu____16744,w,wl1) ->
                                             let w_app =
                                               let uu____16750 =
                                                 let uu____16755 =
                                                   FStar_List.map
                                                     (fun uu____16766  ->
                                                        match uu____16766
                                                        with
                                                        | (z,uu____16774) ->
                                                            let uu____16779 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____16779) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____16755
                                                  in
                                               uu____16750
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____16781 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____16781
                                               then
                                                 let uu____16786 =
                                                   let uu____16790 =
                                                     flex_t_to_string lhs  in
                                                   let uu____16792 =
                                                     let uu____16796 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____16798 =
                                                       let uu____16802 =
                                                         term_to_string w  in
                                                       let uu____16804 =
                                                         let uu____16808 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____16817 =
                                                           let uu____16821 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____16830 =
                                                             let uu____16834
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____16834]
                                                              in
                                                           uu____16821 ::
                                                             uu____16830
                                                            in
                                                         uu____16808 ::
                                                           uu____16817
                                                          in
                                                       uu____16802 ::
                                                         uu____16804
                                                        in
                                                     uu____16796 ::
                                                       uu____16798
                                                      in
                                                   uu____16790 :: uu____16792
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____16786
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____16851 =
                                                     let uu____16856 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____16856)  in
                                                   TERM uu____16851  in
                                                 let uu____16857 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____16857
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____16865 =
                                                        let uu____16870 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____16870)
                                                         in
                                                      TERM uu____16865  in
                                                    [s1; s2])
                                                  in
                                               let uu____16871 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____16871))))))
                   | uu____16872 ->
                       let uu____16889 =
                         FStar_Thunk.mkv "flex-flex: non-patterns"  in
                       giveup_or_defer env orig wl uu____16889)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____16943 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____16943
            then
              let uu____16948 = FStar_Syntax_Print.term_to_string t1  in
              let uu____16950 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____16952 = FStar_Syntax_Print.term_to_string t2  in
              let uu____16954 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____16948 uu____16950 uu____16952 uu____16954
            else ());
           (let uu____16965 = FStar_Syntax_Util.head_and_args t1  in
            match uu____16965 with
            | (head1,args1) ->
                let uu____17008 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17008 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17078 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17078 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17083 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17083)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17104 =
                         mklstr
                           (fun uu____17115  ->
                              let uu____17116 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17118 = args_to_string args1  in
                              let uu____17122 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17124 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17116 uu____17118 uu____17122
                                uu____17124)
                          in
                       giveup env1 uu____17104 orig
                     else
                       (let uu____17131 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17136 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17136 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17131
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2510_17140 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2510_17140.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2510_17140.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2510_17140.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2510_17140.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2510_17140.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2510_17140.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2510_17140.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2510_17140.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17150 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17150
                                    else solve env1 wl2))
                        else
                          (let uu____17155 = base_and_refinement env1 t1  in
                           match uu____17155 with
                           | (base1,refinement1) ->
                               let uu____17180 = base_and_refinement env1 t2
                                  in
                               (match uu____17180 with
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
                                           let uu____17345 =
                                             FStar_List.fold_right
                                               (fun uu____17385  ->
                                                  fun uu____17386  ->
                                                    match (uu____17385,
                                                            uu____17386)
                                                    with
                                                    | (((a1,uu____17438),
                                                        (a2,uu____17440)),
                                                       (probs,wl3)) ->
                                                        let uu____17489 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____17489
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17345 with
                                           | (subprobs,wl3) ->
                                               ((let uu____17532 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17532
                                                 then
                                                   let uu____17537 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____17537
                                                 else ());
                                                (let uu____17543 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____17543
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
                                                    (let uu____17570 =
                                                       mk_sub_probs wl3  in
                                                     match uu____17570 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____17586 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____17586
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____17594 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____17594))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____17619 =
                                                    mk_sub_probs wl3  in
                                                  match uu____17619 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____17635 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____17635
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____17643 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____17643)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____17671 =
                                           match uu____17671 with
                                           | (prob,reason) ->
                                               ((let uu____17688 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17688
                                                 then
                                                   let uu____17693 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____17695 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____17693 uu____17695
                                                 else ());
                                                (let uu____17701 =
                                                   let uu____17710 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____17713 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____17710, uu____17713)
                                                    in
                                                 match uu____17701 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____17726 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____17726 with
                                                      | (head1',uu____17744)
                                                          ->
                                                          let uu____17769 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____17769
                                                           with
                                                           | (head2',uu____17787)
                                                               ->
                                                               let uu____17812
                                                                 =
                                                                 let uu____17817
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____17818
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____17817,
                                                                   uu____17818)
                                                                  in
                                                               (match uu____17812
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____17820
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17820
                                                                    then
                                                                    let uu____17825
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____17827
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____17829
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____17831
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____17825
                                                                    uu____17827
                                                                    uu____17829
                                                                    uu____17831
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____17836
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2598_17844
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2598_17844.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____17846
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____17846
                                                                    then
                                                                    let uu____17851
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____17851
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____17856 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____17868 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____17868 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____17876 =
                                             let uu____17877 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____17877.FStar_Syntax_Syntax.n
                                              in
                                           match uu____17876 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____17882 -> false  in
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
                                          | uu____17885 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____17888 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2618_17924 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2618_17924.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2618_17924.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2618_17924.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2618_17924.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2618_17924.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2618_17924.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2618_17924.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2618_17924.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18000 = destruct_flex_t scrutinee wl1  in
             match uu____18000 with
             | ((_t,uv,_args),wl2) ->
                 let uu____18011 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18011 with
                  | (xs,pat_term,uu____18027,uu____18028) ->
                      let uu____18033 =
                        FStar_List.fold_left
                          (fun uu____18056  ->
                             fun x  ->
                               match uu____18056 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18077 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18077 with
                                    | (uu____18096,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18033 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18117 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18117 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2658_18134 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2658_18134.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2658_18134.umax_heuristic_ok);
                                    tcenv = (uu___2658_18134.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18145 = solve env1 wl'  in
                                (match uu____18145 with
                                 | Success (uu____18148,imps) ->
                                     let wl'1 =
                                       let uu___2666_18151 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2666_18151.wl_deferred);
                                         ctr = (uu___2666_18151.ctr);
                                         defer_ok =
                                           (uu___2666_18151.defer_ok);
                                         smt_ok = (uu___2666_18151.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2666_18151.umax_heuristic_ok);
                                         tcenv = (uu___2666_18151.tcenv);
                                         wl_implicits =
                                           (uu___2666_18151.wl_implicits)
                                       }  in
                                     let uu____18152 = solve env1 wl'1  in
                                     (match uu____18152 with
                                      | Success (uu____18155,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2674_18159 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2674_18159.attempting);
                                                 wl_deferred =
                                                   (uu___2674_18159.wl_deferred);
                                                 ctr = (uu___2674_18159.ctr);
                                                 defer_ok =
                                                   (uu___2674_18159.defer_ok);
                                                 smt_ok =
                                                   (uu___2674_18159.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2674_18159.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2674_18159.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____18160 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18166 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18189 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18189
                 then
                   let uu____18194 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18196 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18194 uu____18196
                 else ());
                (let uu____18201 =
                   let uu____18222 =
                     let uu____18231 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18231)  in
                   let uu____18238 =
                     let uu____18247 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18247)  in
                   (uu____18222, uu____18238)  in
                 match uu____18201 with
                 | ((uu____18277,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18280;
                                   FStar_Syntax_Syntax.vars = uu____18281;_}),
                    (s,t)) ->
                     let uu____18352 =
                       let uu____18354 = is_flex scrutinee  in
                       Prims.op_Negation uu____18354  in
                     if uu____18352
                     then
                       ((let uu____18365 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18365
                         then
                           let uu____18370 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18370
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18389 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18389
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18404 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18404
                           then
                             let uu____18409 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18411 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18409 uu____18411
                           else ());
                          (let pat_discriminates uu___28_18436 =
                             match uu___28_18436 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18452;
                                  FStar_Syntax_Syntax.p = uu____18453;_},FStar_Pervasives_Native.None
                                ,uu____18454) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18468;
                                  FStar_Syntax_Syntax.p = uu____18469;_},FStar_Pervasives_Native.None
                                ,uu____18470) -> true
                             | uu____18497 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____18600 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____18600 with
                                       | (uu____18602,uu____18603,t') ->
                                           let uu____18621 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____18621 with
                                            | (FullMatch ,uu____18633) ->
                                                true
                                            | (HeadMatch
                                               uu____18647,uu____18648) ->
                                                true
                                            | uu____18663 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____18700 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____18700
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____18711 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____18711 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____18799,uu____18800) ->
                                       branches1
                                   | uu____18945 -> branches  in
                                 let uu____19000 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19009 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19009 with
                                        | (p,uu____19013,uu____19014) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19043  -> FStar_Util.Inr _19043)
                                   uu____19000))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19073 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19073 with
                                | (p,uu____19082,e) ->
                                    ((let uu____19101 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19101
                                      then
                                        let uu____19106 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19108 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19106 uu____19108
                                      else ());
                                     (let uu____19113 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19128  -> FStar_Util.Inr _19128)
                                        uu____19113)))))
                 | ((s,t),(uu____19131,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19134;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19135;_}))
                     ->
                     let uu____19204 =
                       let uu____19206 = is_flex scrutinee  in
                       Prims.op_Negation uu____19206  in
                     if uu____19204
                     then
                       ((let uu____19217 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19217
                         then
                           let uu____19222 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19222
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19241 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19241
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19256 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19256
                           then
                             let uu____19261 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19263 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19261 uu____19263
                           else ());
                          (let pat_discriminates uu___28_19288 =
                             match uu___28_19288 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19304;
                                  FStar_Syntax_Syntax.p = uu____19305;_},FStar_Pervasives_Native.None
                                ,uu____19306) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19320;
                                  FStar_Syntax_Syntax.p = uu____19321;_},FStar_Pervasives_Native.None
                                ,uu____19322) -> true
                             | uu____19349 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19452 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19452 with
                                       | (uu____19454,uu____19455,t') ->
                                           let uu____19473 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19473 with
                                            | (FullMatch ,uu____19485) ->
                                                true
                                            | (HeadMatch
                                               uu____19499,uu____19500) ->
                                                true
                                            | uu____19515 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19552 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19552
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19563 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19563 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19651,uu____19652) ->
                                       branches1
                                   | uu____19797 -> branches  in
                                 let uu____19852 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19861 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19861 with
                                        | (p,uu____19865,uu____19866) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19895  -> FStar_Util.Inr _19895)
                                   uu____19852))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19925 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19925 with
                                | (p,uu____19934,e) ->
                                    ((let uu____19953 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19953
                                      then
                                        let uu____19958 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19960 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19958 uu____19960
                                      else ());
                                     (let uu____19965 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19980  -> FStar_Util.Inr _19980)
                                        uu____19965)))))
                 | uu____19981 ->
                     ((let uu____20003 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20003
                       then
                         let uu____20008 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20010 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20008 uu____20010
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20056 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20056
            then
              let uu____20061 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20063 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20065 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20067 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20061 uu____20063 uu____20065 uu____20067
            else ());
           (let uu____20072 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20072 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20103,uu____20104) ->
                     let rec may_relate head3 =
                       let uu____20132 =
                         let uu____20133 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20133.FStar_Syntax_Syntax.n  in
                       match uu____20132 with
                       | FStar_Syntax_Syntax.Tm_name uu____20137 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20139 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20164 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20164 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20166 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20169
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20170 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20173,uu____20174) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20216) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20222) ->
                           may_relate t
                       | uu____20227 -> false  in
                     let uu____20229 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20229 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20242 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20242
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20252 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20252
                          then
                            let uu____20255 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20255 with
                             | (guard,wl2) ->
                                 let uu____20262 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20262)
                          else
                            (let uu____20265 =
                               mklstr
                                 (fun uu____20276  ->
                                    let uu____20277 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20279 =
                                      let uu____20281 =
                                        let uu____20285 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20285
                                          (fun x  ->
                                             let uu____20292 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20292)
                                         in
                                      FStar_Util.dflt "" uu____20281  in
                                    let uu____20297 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20299 =
                                      let uu____20301 =
                                        let uu____20305 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20305
                                          (fun x  ->
                                             let uu____20312 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20312)
                                         in
                                      FStar_Util.dflt "" uu____20301  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20277 uu____20279 uu____20297
                                      uu____20299)
                                in
                             giveup env1 uu____20265 orig))
                 | (HeadMatch (true ),uu____20318) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20333 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20333 with
                        | (guard,wl2) ->
                            let uu____20340 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20340)
                     else
                       (let uu____20343 =
                          mklstr
                            (fun uu____20350  ->
                               let uu____20351 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20353 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20351 uu____20353)
                           in
                        giveup env1 uu____20343 orig)
                 | (uu____20356,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2849_20370 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2849_20370.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2849_20370.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2849_20370.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2849_20370.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2849_20370.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2849_20370.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2849_20370.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2849_20370.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20397 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20397
          then
            let uu____20400 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20400
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20406 =
                let uu____20409 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20409  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20406 t1);
             (let uu____20428 =
                let uu____20431 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20431  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20428 t2);
             (let uu____20450 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____20450
              then
                let uu____20454 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____20456 =
                  let uu____20458 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____20460 =
                    let uu____20462 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____20462  in
                  Prims.op_Hat uu____20458 uu____20460  in
                let uu____20465 =
                  let uu____20467 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____20469 =
                    let uu____20471 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____20471  in
                  Prims.op_Hat uu____20467 uu____20469  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20454 uu____20456 uu____20465
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____20478,uu____20479) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____20495,FStar_Syntax_Syntax.Tm_delayed uu____20496) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____20512,uu____20513) ->
                  let uu____20540 =
                    let uu___2880_20541 = problem  in
                    let uu____20542 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2880_20541.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20542;
                      FStar_TypeChecker_Common.relation =
                        (uu___2880_20541.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2880_20541.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2880_20541.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2880_20541.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2880_20541.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2880_20541.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2880_20541.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2880_20541.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20540 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____20543,uu____20544) ->
                  let uu____20551 =
                    let uu___2886_20552 = problem  in
                    let uu____20553 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2886_20552.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____20553;
                      FStar_TypeChecker_Common.relation =
                        (uu___2886_20552.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2886_20552.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2886_20552.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2886_20552.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2886_20552.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2886_20552.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2886_20552.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2886_20552.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20551 wl
              | (uu____20554,FStar_Syntax_Syntax.Tm_ascribed uu____20555) ->
                  let uu____20582 =
                    let uu___2892_20583 = problem  in
                    let uu____20584 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2892_20583.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2892_20583.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2892_20583.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20584;
                      FStar_TypeChecker_Common.element =
                        (uu___2892_20583.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2892_20583.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2892_20583.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2892_20583.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2892_20583.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2892_20583.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20582 wl
              | (uu____20585,FStar_Syntax_Syntax.Tm_meta uu____20586) ->
                  let uu____20593 =
                    let uu___2898_20594 = problem  in
                    let uu____20595 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2898_20594.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2898_20594.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2898_20594.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____20595;
                      FStar_TypeChecker_Common.element =
                        (uu___2898_20594.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2898_20594.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2898_20594.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2898_20594.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2898_20594.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2898_20594.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____20593 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____20597),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____20599)) ->
                  let uu____20608 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____20608
              | (FStar_Syntax_Syntax.Tm_bvar uu____20609,uu____20610) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____20612,FStar_Syntax_Syntax.Tm_bvar uu____20613) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_20683 =
                    match uu___29_20683 with
                    | [] -> c
                    | bs ->
                        let uu____20711 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____20711
                     in
                  let uu____20722 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____20722 with
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
                                    let uu____20871 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____20871
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
                  let mk_t t l uu___30_20960 =
                    match uu___30_20960 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21002 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21002 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21147 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21148 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21147
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21148 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21150,uu____21151) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21182 -> true
                    | uu____21202 -> false  in
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
                      (let uu____21262 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21270 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21270.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21270.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21270.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21270.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21270.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21270.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21270.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21270.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21270.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21270.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21270.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21270.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21270.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21270.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21270.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21270.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21270.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21270.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21270.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21270.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21270.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21270.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21270.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21270.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21270.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21270.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21270.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21270.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21270.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21270.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21270.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21270.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21270.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21270.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21270.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21270.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21270.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21270.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21270.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21270.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21270.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21270.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21270.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21270.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21262 with
                       | (uu____21275,ty,uu____21277) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21286 =
                                 let uu____21287 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21287.FStar_Syntax_Syntax.n  in
                               match uu____21286 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21290 ->
                                   let uu____21297 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21297
                               | uu____21298 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21301 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21301
                             then
                               let uu____21306 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21308 =
                                 let uu____21310 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21310
                                  in
                               let uu____21311 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21306 uu____21308 uu____21311
                             else ());
                            r1))
                     in
                  let uu____21316 =
                    let uu____21333 = maybe_eta t1  in
                    let uu____21340 = maybe_eta t2  in
                    (uu____21333, uu____21340)  in
                  (match uu____21316 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21382 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21382.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21382.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21382.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21382.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21382.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21382.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21382.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21382.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21403 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21403
                       then
                         let uu____21406 = destruct_flex_t not_abs wl  in
                         (match uu____21406 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21423 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21423.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21423.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21423.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21423.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21423.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21423.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21423.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21423.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21426 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21426 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21449 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21449
                       then
                         let uu____21452 = destruct_flex_t not_abs wl  in
                         (match uu____21452 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21469 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21469.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21469.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21469.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21469.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21469.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21469.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21469.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21469.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21472 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21472 orig))
                   | uu____21475 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____21493,FStar_Syntax_Syntax.Tm_abs uu____21494) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21525 -> true
                    | uu____21545 -> false  in
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
                      (let uu____21605 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3000_21613 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3000_21613.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3000_21613.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3000_21613.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3000_21613.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3000_21613.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3000_21613.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3000_21613.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3000_21613.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3000_21613.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3000_21613.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3000_21613.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3000_21613.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3000_21613.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3000_21613.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3000_21613.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3000_21613.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3000_21613.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3000_21613.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3000_21613.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3000_21613.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3000_21613.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3000_21613.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3000_21613.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3000_21613.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3000_21613.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3000_21613.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3000_21613.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3000_21613.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3000_21613.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3000_21613.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3000_21613.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3000_21613.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3000_21613.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3000_21613.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3000_21613.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3000_21613.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3000_21613.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3000_21613.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3000_21613.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3000_21613.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3000_21613.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3000_21613.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3000_21613.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3000_21613.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____21605 with
                       | (uu____21618,ty,uu____21620) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21629 =
                                 let uu____21630 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21630.FStar_Syntax_Syntax.n  in
                               match uu____21629 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21633 ->
                                   let uu____21640 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21640
                               | uu____21641 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21644 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21644
                             then
                               let uu____21649 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21651 =
                                 let uu____21653 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21653
                                  in
                               let uu____21654 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21649 uu____21651 uu____21654
                             else ());
                            r1))
                     in
                  let uu____21659 =
                    let uu____21676 = maybe_eta t1  in
                    let uu____21683 = maybe_eta t2  in
                    (uu____21676, uu____21683)  in
                  (match uu____21659 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3021_21725 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3021_21725.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3021_21725.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3021_21725.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3021_21725.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3021_21725.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3021_21725.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3021_21725.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3021_21725.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21746 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21746
                       then
                         let uu____21749 = destruct_flex_t not_abs wl  in
                         (match uu____21749 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21766 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21766.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21766.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21766.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21766.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21766.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21766.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21766.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21766.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21769 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21769 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____21792 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21792
                       then
                         let uu____21795 = destruct_flex_t not_abs wl  in
                         (match uu____21795 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3038_21812 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3038_21812.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3038_21812.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3038_21812.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3038_21812.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3038_21812.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3038_21812.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3038_21812.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3038_21812.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21815 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21815 orig))
                   | uu____21818 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____21848 =
                    let uu____21853 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____21853 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3061_21881 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21881.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21881.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21883 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21883.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21883.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____21884,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3061_21899 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3061_21899.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3061_21899.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3063_21901 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3063_21901.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3063_21901.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____21902 -> (x1, x2)  in
                  (match uu____21848 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____21921 = as_refinement false env t11  in
                       (match uu____21921 with
                        | (x12,phi11) ->
                            let uu____21929 = as_refinement false env t21  in
                            (match uu____21929 with
                             | (x22,phi21) ->
                                 ((let uu____21938 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____21938
                                   then
                                     ((let uu____21943 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____21945 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21947 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____21943
                                         uu____21945 uu____21947);
                                      (let uu____21950 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____21952 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____21954 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____21950
                                         uu____21952 uu____21954))
                                   else ());
                                  (let uu____21959 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____21959 with
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
                                         let uu____22030 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22030
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22042 =
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
                                         (let uu____22055 =
                                            let uu____22058 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22058
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22055
                                            (p_guard base_prob));
                                         (let uu____22077 =
                                            let uu____22080 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22080
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22077
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22099 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22099)
                                          in
                                       let has_uvars =
                                         (let uu____22104 =
                                            let uu____22106 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22106
                                             in
                                          Prims.op_Negation uu____22104) ||
                                           (let uu____22110 =
                                              let uu____22112 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22112
                                               in
                                            Prims.op_Negation uu____22110)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22116 =
                                           let uu____22121 =
                                             let uu____22130 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22130]  in
                                           mk_t_problem wl1 uu____22121 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22116 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22153 =
                                                solve env1
                                                  (let uu___3106_22155 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3106_22155.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3106_22155.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3106_22155.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3106_22155.tcenv);
                                                     wl_implicits =
                                                       (uu___3106_22155.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22153 with
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
                                               | Success uu____22170 ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22179 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22179
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3119_22188 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3119_22188.attempting);
                                                         wl_deferred =
                                                           (uu___3119_22188.wl_deferred);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3119_22188.defer_ok);
                                                         smt_ok =
                                                           (uu___3119_22188.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3119_22188.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3119_22188.tcenv);
                                                         wl_implicits =
                                                           (uu___3119_22188.wl_implicits)
                                                       }  in
                                                     let uu____22190 =
                                                       attempt [base_prob]
                                                         wl4
                                                        in
                                                     solve env1 uu____22190))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22193,FStar_Syntax_Syntax.Tm_uvar uu____22194) ->
                  let uu____22219 = destruct_flex_t t1 wl  in
                  (match uu____22219 with
                   | (f1,wl1) ->
                       let uu____22226 = destruct_flex_t t2 wl1  in
                       (match uu____22226 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22233;
                    FStar_Syntax_Syntax.pos = uu____22234;
                    FStar_Syntax_Syntax.vars = uu____22235;_},uu____22236),FStar_Syntax_Syntax.Tm_uvar
                 uu____22237) ->
                  let uu____22286 = destruct_flex_t t1 wl  in
                  (match uu____22286 with
                   | (f1,wl1) ->
                       let uu____22293 = destruct_flex_t t2 wl1  in
                       (match uu____22293 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22300,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22301;
                    FStar_Syntax_Syntax.pos = uu____22302;
                    FStar_Syntax_Syntax.vars = uu____22303;_},uu____22304))
                  ->
                  let uu____22353 = destruct_flex_t t1 wl  in
                  (match uu____22353 with
                   | (f1,wl1) ->
                       let uu____22360 = destruct_flex_t t2 wl1  in
                       (match uu____22360 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22367;
                    FStar_Syntax_Syntax.pos = uu____22368;
                    FStar_Syntax_Syntax.vars = uu____22369;_},uu____22370),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22371;
                    FStar_Syntax_Syntax.pos = uu____22372;
                    FStar_Syntax_Syntax.vars = uu____22373;_},uu____22374))
                  ->
                  let uu____22447 = destruct_flex_t t1 wl  in
                  (match uu____22447 with
                   | (f1,wl1) ->
                       let uu____22454 = destruct_flex_t t2 wl1  in
                       (match uu____22454 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22461,uu____22462) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22475 = destruct_flex_t t1 wl  in
                  (match uu____22475 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22482;
                    FStar_Syntax_Syntax.pos = uu____22483;
                    FStar_Syntax_Syntax.vars = uu____22484;_},uu____22485),uu____22486)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____22523 = destruct_flex_t t1 wl  in
                  (match uu____22523 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____22530,FStar_Syntax_Syntax.Tm_uvar uu____22531) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____22544,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22545;
                    FStar_Syntax_Syntax.pos = uu____22546;
                    FStar_Syntax_Syntax.vars = uu____22547;_},uu____22548))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22585,FStar_Syntax_Syntax.Tm_arrow uu____22586) ->
                  solve_t' env
                    (let uu___3219_22614 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22614.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22614.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22614.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22614.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22614.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22614.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22614.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22614.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22614.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22615;
                    FStar_Syntax_Syntax.pos = uu____22616;
                    FStar_Syntax_Syntax.vars = uu____22617;_},uu____22618),FStar_Syntax_Syntax.Tm_arrow
                 uu____22619) ->
                  solve_t' env
                    (let uu___3219_22671 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3219_22671.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3219_22671.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3219_22671.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3219_22671.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3219_22671.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3219_22671.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3219_22671.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3219_22671.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3219_22671.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22672,FStar_Syntax_Syntax.Tm_uvar uu____22673) ->
                  let uu____22686 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22686
              | (uu____22687,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22688;
                    FStar_Syntax_Syntax.pos = uu____22689;
                    FStar_Syntax_Syntax.vars = uu____22690;_},uu____22691))
                  ->
                  let uu____22728 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22728
              | (FStar_Syntax_Syntax.Tm_uvar uu____22729,uu____22730) ->
                  let uu____22743 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22743
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22744;
                    FStar_Syntax_Syntax.pos = uu____22745;
                    FStar_Syntax_Syntax.vars = uu____22746;_},uu____22747),uu____22748)
                  ->
                  let uu____22785 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____22785
              | (FStar_Syntax_Syntax.Tm_refine uu____22786,uu____22787) ->
                  let t21 =
                    let uu____22795 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____22795  in
                  solve_t env
                    (let uu___3254_22821 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3254_22821.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3254_22821.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3254_22821.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3254_22821.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3254_22821.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3254_22821.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3254_22821.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3254_22821.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3254_22821.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____22822,FStar_Syntax_Syntax.Tm_refine uu____22823) ->
                  let t11 =
                    let uu____22831 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____22831  in
                  solve_t env
                    (let uu___3261_22857 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3261_22857.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3261_22857.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3261_22857.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3261_22857.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3261_22857.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3261_22857.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3261_22857.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3261_22857.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3261_22857.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____22939 =
                    let uu____22940 = guard_of_prob env wl problem t1 t2  in
                    match uu____22940 with
                    | (guard,wl1) ->
                        let uu____22947 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____22947
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23166 = br1  in
                        (match uu____23166 with
                         | (p1,w1,uu____23195) ->
                             let uu____23212 = br2  in
                             (match uu____23212 with
                              | (p2,w2,uu____23235) ->
                                  let uu____23240 =
                                    let uu____23242 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23242  in
                                  if uu____23240
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23269 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23269 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23306 = br2  in
                                         (match uu____23306 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23339 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23339
                                                 in
                                              let uu____23344 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23375,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23396) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____23455 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____23455 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23344
                                                (fun uu____23527  ->
                                                   match uu____23527 with
                                                   | (wprobs,wl2) ->
                                                       let uu____23564 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____23564
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____23585
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____23585
                                                              then
                                                                let uu____23590
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____23592
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____23590
                                                                  uu____23592
                                                              else ());
                                                             (let uu____23598
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____23598
                                                                (fun
                                                                   uu____23634
                                                                    ->
                                                                   match uu____23634
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
                    | uu____23763 -> FStar_Pervasives_Native.None  in
                  let uu____23804 = solve_branches wl brs1 brs2  in
                  (match uu____23804 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____23830 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____23830 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____23857 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____23857 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____23891 =
                                FStar_List.map
                                  (fun uu____23903  ->
                                     match uu____23903 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____23891  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____23912 =
                              let uu____23913 =
                                let uu____23914 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____23914
                                  (let uu___3360_23922 = wl3  in
                                   {
                                     attempting =
                                       (uu___3360_23922.attempting);
                                     wl_deferred =
                                       (uu___3360_23922.wl_deferred);
                                     ctr = (uu___3360_23922.ctr);
                                     defer_ok = (uu___3360_23922.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3360_23922.umax_heuristic_ok);
                                     tcenv = (uu___3360_23922.tcenv);
                                     wl_implicits =
                                       (uu___3360_23922.wl_implicits)
                                   })
                                 in
                              solve env uu____23913  in
                            (match uu____23912 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____23927 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____23936 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____23936 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____23939,uu____23940) ->
                  let head1 =
                    let uu____23964 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____23964
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24010 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24010
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24056 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24056
                    then
                      let uu____24060 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24062 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24064 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24060 uu____24062 uu____24064
                    else ());
                   (let no_free_uvars t =
                      (let uu____24078 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24078) &&
                        (let uu____24082 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24082)
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
                      let uu____24101 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24101 = FStar_Syntax_Util.Equal  in
                    let uu____24102 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24102
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24106 = equal t1 t2  in
                         (if uu____24106
                          then
                            let uu____24109 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24109
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24114 =
                            let uu____24121 = equal t1 t2  in
                            if uu____24121
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24134 = mk_eq2 wl env orig t1 t2  in
                               match uu____24134 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24114 with
                          | (guard,wl1) ->
                              let uu____24155 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24155))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24158,uu____24159) ->
                  let head1 =
                    let uu____24167 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24167
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24213 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24213
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24259 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24259
                    then
                      let uu____24263 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24265 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24267 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24263 uu____24265 uu____24267
                    else ());
                   (let no_free_uvars t =
                      (let uu____24281 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24281) &&
                        (let uu____24285 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24285)
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
                      let uu____24304 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24304 = FStar_Syntax_Util.Equal  in
                    let uu____24305 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24305
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24309 = equal t1 t2  in
                         (if uu____24309
                          then
                            let uu____24312 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24312
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24317 =
                            let uu____24324 = equal t1 t2  in
                            if uu____24324
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24337 = mk_eq2 wl env orig t1 t2  in
                               match uu____24337 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24317 with
                          | (guard,wl1) ->
                              let uu____24358 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24358))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24361,uu____24362) ->
                  let head1 =
                    let uu____24364 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24364
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24410 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24410
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24456 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24456
                    then
                      let uu____24460 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24462 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24464 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24460 uu____24462 uu____24464
                    else ());
                   (let no_free_uvars t =
                      (let uu____24478 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24478) &&
                        (let uu____24482 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24482)
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
                      let uu____24501 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24501 = FStar_Syntax_Util.Equal  in
                    let uu____24502 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24502
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24506 = equal t1 t2  in
                         (if uu____24506
                          then
                            let uu____24509 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24509
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24514 =
                            let uu____24521 = equal t1 t2  in
                            if uu____24521
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24534 = mk_eq2 wl env orig t1 t2  in
                               match uu____24534 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24514 with
                          | (guard,wl1) ->
                              let uu____24555 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24555))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____24558,uu____24559) ->
                  let head1 =
                    let uu____24561 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24561
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24607 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24607
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24653 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24653
                    then
                      let uu____24657 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24659 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24661 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24657 uu____24659 uu____24661
                    else ());
                   (let no_free_uvars t =
                      (let uu____24675 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24675) &&
                        (let uu____24679 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24679)
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
                      let uu____24698 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24698 = FStar_Syntax_Util.Equal  in
                    let uu____24699 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24699
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24703 = equal t1 t2  in
                         (if uu____24703
                          then
                            let uu____24706 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24706
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24711 =
                            let uu____24718 = equal t1 t2  in
                            if uu____24718
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24731 = mk_eq2 wl env orig t1 t2  in
                               match uu____24731 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24711 with
                          | (guard,wl1) ->
                              let uu____24752 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24752))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____24755,uu____24756) ->
                  let head1 =
                    let uu____24758 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24758
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24804 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24804
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24850 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24850
                    then
                      let uu____24854 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24856 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24858 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24854 uu____24856 uu____24858
                    else ());
                   (let no_free_uvars t =
                      (let uu____24872 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24872) &&
                        (let uu____24876 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24876)
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
                      let uu____24895 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24895 = FStar_Syntax_Util.Equal  in
                    let uu____24896 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24896
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24900 = equal t1 t2  in
                         (if uu____24900
                          then
                            let uu____24903 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24903
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24908 =
                            let uu____24915 = equal t1 t2  in
                            if uu____24915
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24928 = mk_eq2 wl env orig t1 t2  in
                               match uu____24928 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24908 with
                          | (guard,wl1) ->
                              let uu____24949 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24949))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____24952,uu____24953) ->
                  let head1 =
                    let uu____24971 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24971
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25017 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25017
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25063 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25063
                    then
                      let uu____25067 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25069 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25071 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25067 uu____25069 uu____25071
                    else ());
                   (let no_free_uvars t =
                      (let uu____25085 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25085) &&
                        (let uu____25089 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25089)
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
                      let uu____25108 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25108 = FStar_Syntax_Util.Equal  in
                    let uu____25109 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25109
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25113 = equal t1 t2  in
                         (if uu____25113
                          then
                            let uu____25116 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25116
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25121 =
                            let uu____25128 = equal t1 t2  in
                            if uu____25128
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25141 = mk_eq2 wl env orig t1 t2  in
                               match uu____25141 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25121 with
                          | (guard,wl1) ->
                              let uu____25162 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25162))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25165,FStar_Syntax_Syntax.Tm_match uu____25166) ->
                  let head1 =
                    let uu____25190 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25190
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25236 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25236
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25282 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25282
                    then
                      let uu____25286 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25288 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25290 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25286 uu____25288 uu____25290
                    else ());
                   (let no_free_uvars t =
                      (let uu____25304 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25304) &&
                        (let uu____25308 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25308)
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
                      let uu____25327 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25327 = FStar_Syntax_Util.Equal  in
                    let uu____25328 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25328
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25332 = equal t1 t2  in
                         (if uu____25332
                          then
                            let uu____25335 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25335
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25340 =
                            let uu____25347 = equal t1 t2  in
                            if uu____25347
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25360 = mk_eq2 wl env orig t1 t2  in
                               match uu____25360 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25340 with
                          | (guard,wl1) ->
                              let uu____25381 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25381))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25384,FStar_Syntax_Syntax.Tm_uinst uu____25385) ->
                  let head1 =
                    let uu____25393 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25393
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25439 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25439
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25485 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25485
                    then
                      let uu____25489 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25491 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25493 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25489 uu____25491 uu____25493
                    else ());
                   (let no_free_uvars t =
                      (let uu____25507 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25507) &&
                        (let uu____25511 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25511)
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
                      let uu____25530 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25530 = FStar_Syntax_Util.Equal  in
                    let uu____25531 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25531
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25535 = equal t1 t2  in
                         (if uu____25535
                          then
                            let uu____25538 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25538
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25543 =
                            let uu____25550 = equal t1 t2  in
                            if uu____25550
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25563 = mk_eq2 wl env orig t1 t2  in
                               match uu____25563 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25543 with
                          | (guard,wl1) ->
                              let uu____25584 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25584))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25587,FStar_Syntax_Syntax.Tm_name uu____25588) ->
                  let head1 =
                    let uu____25590 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25590
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25636 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25636
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25676 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25676
                    then
                      let uu____25680 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25682 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25684 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25680 uu____25682 uu____25684
                    else ());
                   (let no_free_uvars t =
                      (let uu____25698 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25698) &&
                        (let uu____25702 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25702)
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
                      let uu____25721 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25721 = FStar_Syntax_Util.Equal  in
                    let uu____25722 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25722
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25726 = equal t1 t2  in
                         (if uu____25726
                          then
                            let uu____25729 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25729
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25734 =
                            let uu____25741 = equal t1 t2  in
                            if uu____25741
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25754 = mk_eq2 wl env orig t1 t2  in
                               match uu____25754 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25734 with
                          | (guard,wl1) ->
                              let uu____25775 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25775))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25778,FStar_Syntax_Syntax.Tm_constant uu____25779) ->
                  let head1 =
                    let uu____25781 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25781
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25821 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25821
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25861 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25861
                    then
                      let uu____25865 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25867 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25869 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25865 uu____25867 uu____25869
                    else ());
                   (let no_free_uvars t =
                      (let uu____25883 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25883) &&
                        (let uu____25887 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25887)
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
                      let uu____25906 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25906 = FStar_Syntax_Util.Equal  in
                    let uu____25907 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25907
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25911 = equal t1 t2  in
                         (if uu____25911
                          then
                            let uu____25914 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25914
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25919 =
                            let uu____25926 = equal t1 t2  in
                            if uu____25926
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25939 = mk_eq2 wl env orig t1 t2  in
                               match uu____25939 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25919 with
                          | (guard,wl1) ->
                              let uu____25960 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25960))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25963,FStar_Syntax_Syntax.Tm_fvar uu____25964) ->
                  let head1 =
                    let uu____25966 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25966
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26012 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26012
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26058 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26058
                    then
                      let uu____26062 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26064 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26066 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26062 uu____26064 uu____26066
                    else ());
                   (let no_free_uvars t =
                      (let uu____26080 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26080) &&
                        (let uu____26084 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26084)
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
                      let uu____26103 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26103 = FStar_Syntax_Util.Equal  in
                    let uu____26104 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26104
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26108 = equal t1 t2  in
                         (if uu____26108
                          then
                            let uu____26111 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26111
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26116 =
                            let uu____26123 = equal t1 t2  in
                            if uu____26123
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26136 = mk_eq2 wl env orig t1 t2  in
                               match uu____26136 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26116 with
                          | (guard,wl1) ->
                              let uu____26157 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26157))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26160,FStar_Syntax_Syntax.Tm_app uu____26161) ->
                  let head1 =
                    let uu____26179 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26179
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26219 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26219
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26259 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26259
                    then
                      let uu____26263 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26265 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26267 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26263 uu____26265 uu____26267
                    else ());
                   (let no_free_uvars t =
                      (let uu____26281 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26281) &&
                        (let uu____26285 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26285)
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
                      let uu____26304 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26304 = FStar_Syntax_Util.Equal  in
                    let uu____26305 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26305
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26309 = equal t1 t2  in
                         (if uu____26309
                          then
                            let uu____26312 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26312
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26317 =
                            let uu____26324 = equal t1 t2  in
                            if uu____26324
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26337 = mk_eq2 wl env orig t1 t2  in
                               match uu____26337 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26317 with
                          | (guard,wl1) ->
                              let uu____26358 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26358))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26361,FStar_Syntax_Syntax.Tm_let uu____26362) ->
                  let uu____26389 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26389
                  then
                    let uu____26392 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26392
                  else
                    (let uu____26395 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26395 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26398,uu____26399) ->
                  let uu____26413 =
                    let uu____26419 =
                      let uu____26421 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26423 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26425 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26427 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26421 uu____26423 uu____26425 uu____26427
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26419)
                     in
                  FStar_Errors.raise_error uu____26413
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26431,FStar_Syntax_Syntax.Tm_let uu____26432) ->
                  let uu____26446 =
                    let uu____26452 =
                      let uu____26454 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26456 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26458 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26460 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26454 uu____26456 uu____26458 uu____26460
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26452)
                     in
                  FStar_Errors.raise_error uu____26446
                    t1.FStar_Syntax_Syntax.pos
              | uu____26464 ->
                  let uu____26469 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26469 orig))))

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
          (let uu____26535 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____26535
           then
             let uu____26540 =
               let uu____26542 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____26542  in
             let uu____26543 =
               let uu____26545 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____26545  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____26540 uu____26543
           else ());
          (let uu____26549 =
             let uu____26551 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____26551  in
           if uu____26549
           then
             let uu____26554 =
               mklstr
                 (fun uu____26561  ->
                    let uu____26562 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____26564 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____26562 uu____26564)
                in
             giveup env uu____26554 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____26586 =
                  mklstr
                    (fun uu____26593  ->
                       let uu____26594 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____26596 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____26594 uu____26596)
                   in
                giveup env uu____26586 orig)
             else
               (let uu____26601 =
                  FStar_List.fold_left2
                    (fun uu____26622  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____26622 with
                           | (univ_sub_probs,wl1) ->
                               let uu____26643 =
                                 let uu____26648 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____26649 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____26648
                                   FStar_TypeChecker_Common.EQ uu____26649
                                   "effect universes"
                                  in
                               (match uu____26643 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____26601 with
                | (univ_sub_probs,wl1) ->
                    let uu____26669 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____26669 with
                     | (ret_sub_prob,wl2) ->
                         let uu____26677 =
                           FStar_List.fold_right2
                             (fun uu____26714  ->
                                fun uu____26715  ->
                                  fun uu____26716  ->
                                    match (uu____26714, uu____26715,
                                            uu____26716)
                                    with
                                    | ((a1,uu____26760),(a2,uu____26762),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____26795 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____26795 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____26677 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____26822 =
                                  let uu____26825 =
                                    let uu____26828 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____26828
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____26825
                                   in
                                FStar_List.append univ_sub_probs uu____26822
                                 in
                              let guard =
                                let guard =
                                  let uu____26850 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____26850  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3512_26859 = wl3  in
                                {
                                  attempting = (uu___3512_26859.attempting);
                                  wl_deferred = (uu___3512_26859.wl_deferred);
                                  ctr = (uu___3512_26859.ctr);
                                  defer_ok = (uu___3512_26859.defer_ok);
                                  smt_ok = (uu___3512_26859.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3512_26859.umax_heuristic_ok);
                                  tcenv = (uu___3512_26859.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____26861 = attempt sub_probs wl5  in
                              solve env uu____26861))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____26879 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____26879
           then
             let uu____26884 =
               let uu____26886 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26886
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____26888 =
               let uu____26890 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26890
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____26884 uu____26888
           else ());
          (let uu____26895 =
             let uu____26900 =
               let uu____26905 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____26905
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____26900
               (fun uu____26922  ->
                  match uu____26922 with
                  | (c,g) ->
                      let uu____26933 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____26933, g))
              in
           match uu____26895 with
           | (c12,g_lift) ->
               ((let uu____26937 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____26937
                 then
                   let uu____26942 =
                     let uu____26944 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26944
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____26946 =
                     let uu____26948 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____26948
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____26942 uu____26946
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3532_26958 = wl  in
                     {
                       attempting = (uu___3532_26958.attempting);
                       wl_deferred = (uu___3532_26958.wl_deferred);
                       ctr = (uu___3532_26958.ctr);
                       defer_ok = (uu___3532_26958.defer_ok);
                       smt_ok = (uu___3532_26958.smt_ok);
                       umax_heuristic_ok =
                         (uu___3532_26958.umax_heuristic_ok);
                       tcenv = (uu___3532_26958.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____26959 =
                     let rec is_uvar1 t =
                       let uu____26973 =
                         let uu____26974 = FStar_Syntax_Subst.compress t  in
                         uu____26974.FStar_Syntax_Syntax.n  in
                       match uu____26973 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____26978 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____26993) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____26999) ->
                           is_uvar1 t1
                       | uu____27024 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27058  ->
                          fun uu____27059  ->
                            fun uu____27060  ->
                              match (uu____27058, uu____27059, uu____27060)
                              with
                              | ((a1,uu____27104),(a2,uu____27106),(is_sub_probs,wl2))
                                  ->
                                  let uu____27139 = is_uvar1 a1  in
                                  if uu____27139
                                  then
                                    ((let uu____27149 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27149
                                      then
                                        let uu____27154 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27156 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27154 uu____27156
                                      else ());
                                     (let uu____27161 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27161 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____26959 with
                   | (is_sub_probs,wl2) ->
                       let uu____27189 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27189 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27197 =
                              let uu____27202 =
                                let uu____27203 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27203
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27202
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27197 with
                             | (uu____27210,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27221 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27223 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27221 s uu____27223
                                    in
                                 let uu____27226 =
                                   let uu____27255 =
                                     let uu____27256 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27256.FStar_Syntax_Syntax.n  in
                                   match uu____27255 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27316 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27316 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27379 =
                                              let uu____27398 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27398
                                                (fun uu____27502  ->
                                                   match uu____27502 with
                                                   | (l1,l2) ->
                                                       let uu____27575 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____27575))
                                               in
                                            (match uu____27379 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____27680 ->
                                       let uu____27681 =
                                         let uu____27687 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____27687)
                                          in
                                       FStar_Errors.raise_error uu____27681 r
                                    in
                                 (match uu____27226 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____27763 =
                                        let uu____27770 =
                                          let uu____27771 =
                                            let uu____27772 =
                                              let uu____27779 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____27779,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____27772
                                             in
                                          [uu____27771]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____27770
                                          (fun b  ->
                                             let uu____27795 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____27797 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____27799 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____27795 uu____27797
                                               uu____27799) r
                                         in
                                      (match uu____27763 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____27809 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____27809
                                             then
                                               let uu____27814 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____27823 =
                                                          let uu____27825 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____27825
                                                           in
                                                        Prims.op_Hat s
                                                          uu____27823) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____27814
                                             else ());
                                            (let wl4 =
                                               let uu___3604_27833 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3604_27833.attempting);
                                                 wl_deferred =
                                                   (uu___3604_27833.wl_deferred);
                                                 ctr = (uu___3604_27833.ctr);
                                                 defer_ok =
                                                   (uu___3604_27833.defer_ok);
                                                 smt_ok =
                                                   (uu___3604_27833.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3604_27833.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3604_27833.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____27858 =
                                                        let uu____27865 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____27865, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____27858) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____27882 =
                                               let f_sort_is =
                                                 let uu____27892 =
                                                   let uu____27893 =
                                                     let uu____27896 =
                                                       let uu____27897 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____27897.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____27896
                                                      in
                                                   uu____27893.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____27892 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____27908,uu____27909::is)
                                                     ->
                                                     let uu____27951 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____27951
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____27984 ->
                                                     let uu____27985 =
                                                       let uu____27991 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____27991)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____27985 r
                                                  in
                                               let uu____27997 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28032  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28032
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28053 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28053
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____27997
                                                in
                                             match uu____27882 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28078 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28078
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28079 =
                                                   let g_sort_is =
                                                     let uu____28089 =
                                                       let uu____28090 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28090.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28089 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28095,uu____28096::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28156 ->
                                                         let uu____28157 =
                                                           let uu____28163 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28163)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28157 r
                                                      in
                                                   let uu____28169 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28204  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28204
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28225
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28225
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28169
                                                    in
                                                 (match uu____28079 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28252 =
                                                          let uu____28257 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28258 =
                                                            let uu____28259 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28259
                                                             in
                                                          (uu____28257,
                                                            uu____28258)
                                                           in
                                                        match uu____28252
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28287 =
                                                          let uu____28290 =
                                                            let uu____28293 =
                                                              let uu____28296
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28296
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28293
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28290
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28287
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28320 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28320
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
                                                        let uu____28331 =
                                                          let uu____28334 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28337  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28337)
                                                            uu____28334
                                                           in
                                                        solve_prob orig
                                                          uu____28331 [] wl6
                                                         in
                                                      let uu____28338 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28338))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28361 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28363 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28363]
              | x -> x  in
            let c12 =
              let uu___3670_28366 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3670_28366.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3670_28366.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3670_28366.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3670_28366.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28367 =
              let uu____28372 =
                FStar_All.pipe_right
                  (let uu___3673_28374 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3673_28374.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3673_28374.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3673_28374.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3673_28374.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28372
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28367
              (fun uu____28388  ->
                 match uu____28388 with
                 | (c,g) ->
                     let uu____28395 =
                       let uu____28397 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28397  in
                     if uu____28395
                     then
                       let uu____28400 =
                         let uu____28406 =
                           let uu____28408 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28410 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28408 uu____28410
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28406)
                          in
                       FStar_Errors.raise_error uu____28400 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28416 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28416
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28422 = lift_c1 ()  in
               solve_eq uu____28422 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28431  ->
                         match uu___31_28431 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28436 -> false))
                  in
               let uu____28438 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28468)::uu____28469,(wp2,uu____28471)::uu____28472)
                     -> (wp1, wp2)
                 | uu____28545 ->
                     let uu____28570 =
                       let uu____28576 =
                         let uu____28578 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____28580 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____28578 uu____28580
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____28576)
                        in
                     FStar_Errors.raise_error uu____28570
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28438 with
               | (wpc1,wpc2) ->
                   let uu____28590 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____28590
                   then
                     let uu____28593 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____28593 wl
                   else
                     (let uu____28597 =
                        let uu____28604 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____28604  in
                      match uu____28597 with
                      | (c2_decl,qualifiers) ->
                          let uu____28625 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____28625
                          then
                            let c1_repr =
                              let uu____28632 =
                                let uu____28633 =
                                  let uu____28634 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____28634  in
                                let uu____28635 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28633 uu____28635
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28632
                               in
                            let c2_repr =
                              let uu____28638 =
                                let uu____28639 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____28640 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____28639 uu____28640
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____28638
                               in
                            let uu____28642 =
                              let uu____28647 =
                                let uu____28649 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____28651 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____28649
                                  uu____28651
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____28647
                               in
                            (match uu____28642 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____28657 = attempt [prob] wl2  in
                                 solve env uu____28657)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____28677 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____28677
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____28700 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____28700
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
                                        let uu____28710 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____28710 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____28717 =
                                        let uu____28724 =
                                          let uu____28725 =
                                            let uu____28742 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____28745 =
                                              let uu____28756 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____28756; wpc1_2]  in
                                            (uu____28742, uu____28745)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____28725
                                           in
                                        FStar_Syntax_Syntax.mk uu____28724
                                         in
                                      uu____28717
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
                                     let uu____28805 =
                                       let uu____28812 =
                                         let uu____28813 =
                                           let uu____28830 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____28833 =
                                             let uu____28844 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____28853 =
                                               let uu____28864 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____28864; wpc1_2]  in
                                             uu____28844 :: uu____28853  in
                                           (uu____28830, uu____28833)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____28813
                                          in
                                       FStar_Syntax_Syntax.mk uu____28812  in
                                     uu____28805 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____28918 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____28918
                              then
                                let uu____28923 =
                                  let uu____28925 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____28925
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____28923
                              else ());
                             (let uu____28929 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____28929 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____28938 =
                                      let uu____28941 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _28944  ->
                                           FStar_Pervasives_Native.Some
                                             _28944) uu____28941
                                       in
                                    solve_prob orig uu____28938 [] wl1  in
                                  let uu____28945 = attempt [base_prob] wl2
                                     in
                                  solve env uu____28945))))
           in
        let uu____28946 = FStar_Util.physical_equality c1 c2  in
        if uu____28946
        then
          let uu____28949 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____28949
        else
          ((let uu____28953 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____28953
            then
              let uu____28958 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____28960 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____28958
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____28960
            else ());
           (let uu____28965 =
              let uu____28974 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____28977 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____28974, uu____28977)  in
            match uu____28965 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____28995),FStar_Syntax_Syntax.Total
                    (t2,uu____28997)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29014 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29014 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29016,FStar_Syntax_Syntax.Total uu____29017) ->
                     let uu____29034 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29034 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29038),FStar_Syntax_Syntax.Total
                    (t2,uu____29040)) ->
                     let uu____29057 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29057 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29060),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29062)) ->
                     let uu____29079 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29079 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29082),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29084)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29101 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29101 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29104),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29106)) ->
                     let uu____29123 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29123 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29126,FStar_Syntax_Syntax.Comp uu____29127) ->
                     let uu____29136 =
                       let uu___3797_29139 = problem  in
                       let uu____29142 =
                         let uu____29143 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29143
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29139.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29142;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29139.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29139.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29139.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29139.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29139.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29139.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29139.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29139.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29136 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29144,FStar_Syntax_Syntax.Comp uu____29145) ->
                     let uu____29154 =
                       let uu___3797_29157 = problem  in
                       let uu____29160 =
                         let uu____29161 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29161
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3797_29157.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29160;
                         FStar_TypeChecker_Common.relation =
                           (uu___3797_29157.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3797_29157.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3797_29157.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3797_29157.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3797_29157.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3797_29157.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3797_29157.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3797_29157.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29154 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29162,FStar_Syntax_Syntax.GTotal uu____29163) ->
                     let uu____29172 =
                       let uu___3809_29175 = problem  in
                       let uu____29178 =
                         let uu____29179 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29179
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29175.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29175.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29175.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29178;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29175.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29175.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29175.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29175.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29175.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29175.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29172 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29180,FStar_Syntax_Syntax.Total uu____29181) ->
                     let uu____29190 =
                       let uu___3809_29193 = problem  in
                       let uu____29196 =
                         let uu____29197 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29197
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3809_29193.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3809_29193.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3809_29193.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29196;
                         FStar_TypeChecker_Common.element =
                           (uu___3809_29193.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3809_29193.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3809_29193.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3809_29193.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3809_29193.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3809_29193.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29190 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29198,FStar_Syntax_Syntax.Comp uu____29199) ->
                     let uu____29200 =
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
                     if uu____29200
                     then
                       let uu____29203 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29203 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29210 =
                            let uu____29215 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29215
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29224 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29225 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29224, uu____29225))
                             in
                          match uu____29210 with
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
                           (let uu____29233 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29233
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29241 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29241 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29244 =
                                  mklstr
                                    (fun uu____29251  ->
                                       let uu____29252 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29254 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29252 uu____29254)
                                   in
                                giveup env uu____29244 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29265 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29265 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29315 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29315 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29340 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29371  ->
                match uu____29371 with
                | (u1,u2) ->
                    let uu____29379 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29381 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29379 uu____29381))
         in
      FStar_All.pipe_right uu____29340 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29418,[])) when
          let uu____29445 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29445 -> "{}"
      | uu____29448 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29475 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29475
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____29487 =
              FStar_List.map
                (fun uu____29500  ->
                   match uu____29500 with
                   | (uu____29507,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Common.deferred
               in
            FStar_All.pipe_right uu____29487 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____29518 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____29518 imps
  
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
                  let uu____29575 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____29575
                  then
                    let uu____29583 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____29585 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____29583
                      (rel_to_string rel) uu____29585
                  else "TOP"  in
                let uu____29591 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____29591 with
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
              let uu____29651 =
                let uu____29654 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _29657  -> FStar_Pervasives_Native.Some _29657)
                  uu____29654
                 in
              FStar_Syntax_Syntax.new_bv uu____29651 t1  in
            let uu____29658 =
              let uu____29663 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____29663
               in
            match uu____29658 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____29721 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____29721
         then
           let uu____29726 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____29726
         else ());
        (let uu____29733 =
           FStar_Util.record_time (fun uu____29740  -> solve env probs)  in
         match uu____29733 with
         | (sol,ms) ->
             ((let uu____29752 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____29752
               then
                 let uu____29757 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____29757
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____29770 =
                     FStar_Util.record_time
                       (fun uu____29777  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____29770 with
                    | ((),ms1) ->
                        ((let uu____29788 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____29788
                          then
                            let uu____29793 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____29793
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____29805 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____29805
                     then
                       let uu____29812 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____29812
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
          ((let uu____29838 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____29838
            then
              let uu____29843 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____29843
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____29851 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____29851
             then
               let uu____29856 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____29856
             else ());
            (let f2 =
               let uu____29862 =
                 let uu____29863 = FStar_Syntax_Util.unmeta f1  in
                 uu____29863.FStar_Syntax_Syntax.n  in
               match uu____29862 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____29867 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3926_29868 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred =
                 (uu___3926_29868.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___3926_29868.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___3926_29868.FStar_TypeChecker_Common.implicits)
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
            let uu____29911 =
              let uu____29912 =
                let uu____29913 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _29914  ->
                       FStar_TypeChecker_Common.NonTrivial _29914)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____29913;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____29912  in
            FStar_All.pipe_left
              (fun _29921  -> FStar_Pervasives_Native.Some _29921)
              uu____29911
  
let with_guard_no_simp :
  'Auu____29931 .
    'Auu____29931 ->
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
            let uu____29971 =
              let uu____29972 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _29973  -> FStar_TypeChecker_Common.NonTrivial _29973)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____29972;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____29971
  
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
          (let uu____30006 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30006
           then
             let uu____30011 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30013 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30011
               uu____30013
           else ());
          (let uu____30018 =
             let uu____30023 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30023
              in
           match uu____30018 with
           | (prob,wl) ->
               let g =
                 let uu____30031 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30039  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30031  in
               ((let uu____30057 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30057
                 then
                   let uu____30062 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30062
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
        let uu____30083 = try_teq true env t1 t2  in
        match uu____30083 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30088 = FStar_TypeChecker_Env.get_range env  in
              let uu____30089 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30088 uu____30089);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30097 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30097
              then
                let uu____30102 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30104 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30106 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30102
                  uu____30104 uu____30106
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
        (let uu____30130 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30130
         then
           let uu____30135 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30137 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30135
             uu____30137
         else ());
        (let uu____30142 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30142 with
         | (prob,x,wl) ->
             let g =
               let uu____30157 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30166  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30157  in
             ((let uu____30184 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30184
               then
                 let uu____30189 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30189
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30197 =
                     let uu____30198 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30198 g1  in
                   FStar_Pervasives_Native.Some uu____30197)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30220 = FStar_TypeChecker_Env.get_range env  in
          let uu____30221 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30220 uu____30221
  
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
        (let uu____30250 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30250
         then
           let uu____30255 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30257 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30255 uu____30257
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30268 =
           let uu____30275 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30275 "sub_comp"
            in
         match uu____30268 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30288 =
                 FStar_Util.record_time
                   (fun uu____30300  ->
                      let uu____30301 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30310  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30301)
                  in
               match uu____30288 with
               | (r,ms) ->
                   ((let uu____30338 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30338
                     then
                       let uu____30343 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30345 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30347 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30343 uu____30345
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30347
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
      fun uu____30385  ->
        match uu____30385 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30428 =
                 let uu____30434 =
                   let uu____30436 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____30438 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30436 uu____30438
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30434)  in
               let uu____30442 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____30428 uu____30442)
               in
            let equiv1 v1 v' =
              let uu____30455 =
                let uu____30460 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____30461 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____30460, uu____30461)  in
              match uu____30455 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____30481 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____30512 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____30512 with
                      | FStar_Syntax_Syntax.U_unif uu____30519 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____30548  ->
                                    match uu____30548 with
                                    | (u,v') ->
                                        let uu____30557 = equiv1 v1 v'  in
                                        if uu____30557
                                        then
                                          let uu____30562 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____30562 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____30583 -> []))
               in
            let uu____30588 =
              let wl =
                let uu___4037_30592 = empty_worklist env  in
                {
                  attempting = (uu___4037_30592.attempting);
                  wl_deferred = (uu___4037_30592.wl_deferred);
                  ctr = (uu___4037_30592.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4037_30592.smt_ok);
                  umax_heuristic_ok = (uu___4037_30592.umax_heuristic_ok);
                  tcenv = (uu___4037_30592.tcenv);
                  wl_implicits = (uu___4037_30592.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____30611  ->
                      match uu____30611 with
                      | (lb,v1) ->
                          let uu____30618 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____30618 with
                           | USolved wl1 -> ()
                           | uu____30621 -> fail1 lb v1)))
               in
            let rec check_ineq uu____30632 =
              match uu____30632 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____30644) -> true
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
                      uu____30668,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____30670,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____30681) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____30689,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____30698 -> false)
               in
            let uu____30704 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____30721  ->
                      match uu____30721 with
                      | (u,v1) ->
                          let uu____30729 = check_ineq (u, v1)  in
                          if uu____30729
                          then true
                          else
                            ((let uu____30737 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____30737
                              then
                                let uu____30742 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____30744 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____30742
                                  uu____30744
                              else ());
                             false)))
               in
            if uu____30704
            then ()
            else
              ((let uu____30754 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____30754
                then
                  ((let uu____30760 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____30760);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____30772 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____30772))
                else ());
               (let uu____30785 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____30785))
  
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
        let fail1 uu____30858 =
          match uu____30858 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4114_30881 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4114_30881.attempting);
            wl_deferred = (uu___4114_30881.wl_deferred);
            ctr = (uu___4114_30881.ctr);
            defer_ok;
            smt_ok = (uu___4114_30881.smt_ok);
            umax_heuristic_ok = (uu___4114_30881.umax_heuristic_ok);
            tcenv = (uu___4114_30881.tcenv);
            wl_implicits = (uu___4114_30881.wl_implicits)
          }  in
        (let uu____30884 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30884
         then
           let uu____30889 = FStar_Util.string_of_bool defer_ok  in
           let uu____30891 = wl_to_string wl  in
           let uu____30893 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____30889 uu____30891 uu____30893
         else ());
        (let g1 =
           let uu____30899 = solve_and_commit env wl fail1  in
           match uu____30899 with
           | FStar_Pervasives_Native.Some
               (uu____30906::uu____30907,uu____30908) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4129_30937 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4129_30937.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4129_30937.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____30938 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4134_30947 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4134_30947.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4134_30947.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4134_30947.FStar_TypeChecker_Common.implicits)
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
            let uu___4146_31024 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Common.deferred =
                (uu___4146_31024.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4146_31024.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits =
                (uu___4146_31024.FStar_TypeChecker_Common.implicits)
            }  in
          let uu____31025 =
            let uu____31027 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31027  in
          if uu____31025
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Common.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31039 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31040 =
                       let uu____31042 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31042
                        in
                     FStar_Errors.diag uu____31039 uu____31040)
                  else ();
                  (let vc1 =
                     let uu____31048 =
                       let uu____31052 =
                         let uu____31054 =
                           FStar_TypeChecker_Env.current_module env  in
                         FStar_Ident.string_of_lid uu____31054  in
                       FStar_Pervasives_Native.Some uu____31052  in
                     FStar_Profiling.profile
                       (fun uu____31057  ->
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Eager_unfolding;
                            FStar_TypeChecker_Env.Simplify;
                            FStar_TypeChecker_Env.Primops] env vc)
                       uu____31048 "FStar.TypeChecker.Rel.vc_normalization"
                      in
                   if debug1
                   then
                     (let uu____31061 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31062 =
                        let uu____31064 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31064
                         in
                      FStar_Errors.diag uu____31061 uu____31062)
                   else ();
                   (let uu____31070 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31070
                      "discharge_guard'" env vc1);
                   (let uu____31072 =
                      FStar_TypeChecker_Common.check_trivial vc1  in
                    match uu____31072 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31081 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31082 =
                                let uu____31084 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31084
                                 in
                              FStar_Errors.diag uu____31081 uu____31082)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31094 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31095 =
                                let uu____31097 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31097
                                 in
                              FStar_Errors.diag uu____31094 uu____31095)
                           else ();
                           (let vcs =
                              let uu____31111 = FStar_Options.use_tactics ()
                                 in
                              if uu____31111
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31133  ->
                                     (let uu____31135 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31135);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31179  ->
                                              match uu____31179 with
                                              | (env1,goal,opts) ->
                                                  let uu____31195 =
                                                    norm_with_steps
                                                      "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31195, opts)))))
                              else
                                (let uu____31199 =
                                   let uu____31206 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31206)  in
                                 [uu____31199])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31239  ->
                                    match uu____31239 with
                                    | (env1,goal,opts) ->
                                        let uu____31249 =
                                          FStar_TypeChecker_Common.check_trivial
                                            goal
                                           in
                                        (match uu____31249 with
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
                                                (let uu____31260 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31261 =
                                                   let uu____31263 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____31265 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31263 uu____31265
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31260 uu____31261)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____31272 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31273 =
                                                   let uu____31275 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____31275
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31272 uu____31273)
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
      let uu____31293 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31293 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31302 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31302
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31316 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31316 with
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
        let uu____31346 = try_teq false env t1 t2  in
        match uu____31346 with
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
            let uu____31390 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____31390 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____31403 ->
                     let uu____31416 =
                       let uu____31417 = FStar_Syntax_Subst.compress r  in
                       uu____31417.FStar_Syntax_Syntax.n  in
                     (match uu____31416 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____31422) ->
                          unresolved ctx_u'
                      | uu____31439 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____31463 = acc  in
            match uu____31463 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____31482 = hd1  in
                     (match uu____31482 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____31493 = unresolved ctx_u  in
                             if uu____31493
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____31517 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____31517
                                     then
                                       let uu____31521 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____31521
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____31530 = teq_nosmt env1 t tm
                                          in
                                       match uu____31530 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4259_31540 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4259_31540.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4262_31548 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4262_31548.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4262_31548.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4262_31548.FStar_TypeChecker_Common.imp_range)
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
                                    let uu___4266_31559 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4266_31559.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4266_31559.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4266_31559.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4266_31559.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4266_31559.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4266_31559.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4266_31559.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4266_31559.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4266_31559.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4266_31559.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4266_31559.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4266_31559.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4266_31559.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4266_31559.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4266_31559.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4266_31559.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4266_31559.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4266_31559.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4266_31559.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4266_31559.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4266_31559.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4266_31559.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4266_31559.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4266_31559.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4266_31559.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4266_31559.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4266_31559.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4266_31559.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4266_31559.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4266_31559.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4266_31559.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4266_31559.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4266_31559.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4266_31559.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4266_31559.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4266_31559.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4266_31559.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4266_31559.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4266_31559.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4266_31559.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4266_31559.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4266_31559.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4266_31559.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4266_31559.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4266_31559.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4266_31559.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4271_31564 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4271_31564.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4271_31564.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4271_31564.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4271_31564.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4271_31564.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4271_31564.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4271_31564.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4271_31564.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4271_31564.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4271_31564.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4271_31564.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4271_31564.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4271_31564.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4271_31564.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4271_31564.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4271_31564.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4271_31564.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4271_31564.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4271_31564.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4271_31564.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4271_31564.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4271_31564.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4271_31564.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4271_31564.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4271_31564.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4271_31564.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4271_31564.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4271_31564.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4271_31564.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4271_31564.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4271_31564.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4271_31564.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4271_31564.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4271_31564.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4271_31564.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4271_31564.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4271_31564.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____31569 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____31569
                                   then
                                     let uu____31574 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____31576 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____31578 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____31580 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____31574 uu____31576 uu____31578
                                       reason uu____31580
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4277_31587  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____31594 =
                                             let uu____31604 =
                                               let uu____31612 =
                                                 let uu____31614 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____31616 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____31618 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____31614 uu____31616
                                                   uu____31618
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____31612, r)
                                                in
                                             [uu____31604]  in
                                           FStar_Errors.add_errors
                                             uu____31594);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____31637 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____31648  ->
                                               let uu____31649 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____31651 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____31653 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____31649 uu____31651
                                                 reason uu____31653)) env2 g1
                                         true
                                        in
                                     match uu____31637 with
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
          let uu___4289_31661 = g  in
          let uu____31662 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4289_31661.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred =
              (uu___4289_31661.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4289_31661.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____31662
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
        let uu____31702 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____31702 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Common.implicits with
      | [] ->
          let uu____31703 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____31703
      | imp::uu____31705 ->
          let uu____31708 =
            let uu____31714 =
              let uu____31716 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____31718 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____31716 uu____31718
                imp.FStar_TypeChecker_Common.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____31714)
             in
          FStar_Errors.raise_error uu____31708
            imp.FStar_TypeChecker_Common.imp_range
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31738 = teq env t1 t2  in
        force_trivial_guard env uu____31738
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31757 = teq_nosmt env t1 t2  in
        match uu____31757 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4314_31776 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4314_31776.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred =
          (uu___4314_31776.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4314_31776.FStar_TypeChecker_Common.implicits)
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
        (let uu____31812 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31812
         then
           let uu____31817 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____31819 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____31817
             uu____31819
         else ());
        (let uu____31824 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____31824 with
         | (prob,x,wl) ->
             let g =
               let uu____31843 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____31852  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____31843  in
             ((let uu____31870 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____31870
               then
                 let uu____31875 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____31877 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____31879 =
                   let uu____31881 = FStar_Util.must g  in
                   guard_to_string env uu____31881  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____31875 uu____31877 uu____31879
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
        let uu____31918 = check_subtyping env t1 t2  in
        match uu____31918 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31937 =
              let uu____31938 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____31938 g  in
            FStar_Pervasives_Native.Some uu____31937
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____31957 = check_subtyping env t1 t2  in
        match uu____31957 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____31976 =
              let uu____31977 =
                let uu____31978 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____31978]  in
              FStar_TypeChecker_Env.close_guard env uu____31977 g  in
            FStar_Pervasives_Native.Some uu____31976
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32016 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32016
         then
           let uu____32021 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32023 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32021
             uu____32023
         else ());
        (let uu____32028 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32028 with
         | (prob,x,wl) ->
             let g =
               let uu____32043 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32052  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32043  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32073 =
                      let uu____32074 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32074]  in
                    FStar_TypeChecker_Env.close_guard env uu____32073 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32115 = subtype_nosmt env t1 t2  in
        match uu____32115 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  