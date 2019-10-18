open Prims
let (inverse_pairs :
  (FStar_Syntax_Syntax.fv * Prims.int * Prims.int * FStar_Syntax_Syntax.fv)
    Prims.list)
  =
  let uu____20 =
    let uu____31 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reveal
        (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
        FStar_Pervasives_Native.None
       in
    let uu____33 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.hide
        (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
        FStar_Pervasives_Native.None
       in
    (uu____31, Prims.int_one, Prims.int_one, uu____33)  in
  let uu____39 =
    let uu____52 =
      let uu____63 =
        FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.hide
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
          FStar_Pervasives_Native.None
         in
      let uu____65 =
        FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.reveal
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_zero)
          FStar_Pervasives_Native.None
         in
      (uu____63, Prims.int_one, Prims.int_one, uu____65)  in
    [uu____52]  in
  uu____20 :: uu____39 
let (lookup_inverses :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list * FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.ctx_uvar *
      (FStar_Syntax_Syntax.subst_elt Prims.list Prims.list *
      FStar_Syntax_Syntax.maybe_set_use_range)) * FStar_Syntax_Syntax.fv)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let lookup1 fv =
      let p =
        FStar_All.pipe_right inverse_pairs
          (FStar_List.find
             (fun uu____209  ->
                match uu____209 with
                | (fv_elmt,uu____222,uu____223,uu____224) ->
                    FStar_Syntax_Syntax.fv_eq fv fv_elmt))
         in
      match p with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu____257,num_univs,num_args,inv_fv) ->
          FStar_Pervasives_Native.Some (num_univs, num_args, inv_fv)
       in
    let is_uvar1 t1 =
      let uu____305 =
        let uu____306 = FStar_Syntax_Subst.compress t1  in
        uu____306.FStar_Syntax_Syntax.n  in
      match uu____305 with
      | FStar_Syntax_Syntax.Tm_uvar u -> FStar_Pervasives_Native.Some u
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar u;
             FStar_Syntax_Syntax.pos = uu____349;
             FStar_Syntax_Syntax.vars = uu____350;_},uu____351)
          -> FStar_Pervasives_Native.Some u
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar u;
             FStar_Syntax_Syntax.pos = uu____381;
             FStar_Syntax_Syntax.vars = uu____382;_},uu____383)
          -> FStar_Pervasives_Native.Some u
      | uu____432 -> FStar_Pervasives_Native.None  in
    let is_fv_app =
      let uu____464 =
        let uu____465 = FStar_Syntax_Subst.compress t  in
        uu____465.FStar_Syntax_Syntax.n  in
      match uu____464 with
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____487;
             FStar_Syntax_Syntax.vars = uu____488;_},args)
          -> FStar_Pervasives_Native.Some (fv, [], args)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____541;
                  FStar_Syntax_Syntax.vars = uu____542;_},univs1);
             FStar_Syntax_Syntax.pos = uu____544;
             FStar_Syntax_Syntax.vars = uu____545;_},args)
          -> FStar_Pervasives_Native.Some (fv, univs1, args)
      | uu____601 -> FStar_Pervasives_Native.None  in
    if is_fv_app = FStar_Pervasives_Native.None
    then FStar_Pervasives_Native.None
    else
      (let uu____721 = FStar_All.pipe_right is_fv_app FStar_Util.must  in
       match uu____721 with
       | (fv,univs1,args) ->
           let in_inverses = lookup1 fv  in
           if in_inverses = FStar_Pervasives_Native.None
           then FStar_Pervasives_Native.None
           else
             (let uu____943 =
                FStar_All.pipe_right in_inverses FStar_Util.must  in
              match uu____943 with
              | (num_univs,num_additional_args,inv_fv) ->
                  if
                    ((FStar_List.length univs1) <> num_univs) ||
                      ((FStar_List.length args) <>
                         (num_additional_args + Prims.int_one))
                  then FStar_Pervasives_Native.None
                  else
                    (let uu____1097 =
                       let uu____1110 =
                         FStar_List.splitAt
                           ((FStar_List.length args) - Prims.int_one) args
                          in
                       FStar_All.pipe_right uu____1110
                         (fun uu____1180  ->
                            match uu____1180 with
                            | (l1,x::uu____1215) ->
                                (l1, (FStar_Pervasives_Native.fst x)))
                        in
                     match uu____1097 with
                     | (additional_args,last_arg) ->
                         let uu____1322 =
                           let uu____1324 = is_uvar1 last_arg  in
                           uu____1324 = FStar_Pervasives_Native.None  in
                         if uu____1322
                         then FStar_Pervasives_Native.None
                         else
                           (let uu____1434 =
                              let uu____1467 =
                                let uu____1480 = is_uvar1 last_arg  in
                                FStar_All.pipe_right uu____1480
                                  FStar_Util.must
                                 in
                              (univs1, additional_args, last_arg, uu____1467,
                                inv_fv)
                               in
                            FStar_Pervasives_Native.Some uu____1434))))
  
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____1626 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____1661 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  umax_heuristic_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env ;
  wl_implicits: FStar_TypeChecker_Env.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; ctr; defer_ok; smt_ok; umax_heuristic_ok;
        tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list)
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
  worklist -> FStar_TypeChecker_Env.implicits) =
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
                    let uu____2084 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____2084;
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
                       FStar_TypeChecker_Env.imp_reason = reason;
                       FStar_TypeChecker_Env.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Env.imp_tm = t;
                       FStar_TypeChecker_Env.imp_range = r
                     }  in
                   (ctx_uvar, t,
                     (let uu___151_2116 = wl  in
                      {
                        attempting = (uu___151_2116.attempting);
                        wl_deferred = (uu___151_2116.wl_deferred);
                        ctr = (uu___151_2116.ctr);
                        defer_ok = (uu___151_2116.defer_ok);
                        smt_ok = (uu___151_2116.smt_ok);
                        umax_heuristic_ok = (uu___151_2116.umax_heuristic_ok);
                        tcenv = (uu___151_2116.tcenv);
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
            let uu___157_2149 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___157_2149.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___157_2149.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___157_2149.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___157_2149.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___157_2149.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___157_2149.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___157_2149.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___157_2149.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___157_2149.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___157_2149.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___157_2149.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___157_2149.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___157_2149.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___157_2149.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___157_2149.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___157_2149.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___157_2149.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___157_2149.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___157_2149.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___157_2149.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___157_2149.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___157_2149.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___157_2149.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___157_2149.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___157_2149.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___157_2149.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___157_2149.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___157_2149.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___157_2149.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___157_2149.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___157_2149.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___157_2149.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___157_2149.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___157_2149.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___157_2149.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___157_2149.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___157_2149.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___157_2149.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___157_2149.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___157_2149.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___157_2149.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___157_2149.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___157_2149.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___157_2149.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____2151 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____2151 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Env.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____2194 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____2230 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____2263 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____2274 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____2285 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_2303  ->
    match uu___0_2303 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____2315 = FStar_Syntax_Util.head_and_args t  in
    match uu____2315 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____2378 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____2380 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____2395 =
                     let uu____2397 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____2397  in
                   FStar_Util.format1 "@<%s>" uu____2395
                in
             let uu____2401 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____2378 uu____2380 uu____2401
         | uu____2404 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_2416  ->
      match uu___1_2416 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2421 =
            let uu____2425 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____2427 =
              let uu____2431 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____2433 =
                let uu____2437 =
                  let uu____2441 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____2441]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____2437
                 in
              uu____2431 :: uu____2433  in
            uu____2425 :: uu____2427  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____2421
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2452 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2454 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2456 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____2452 uu____2454
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2456
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_2470  ->
      match uu___2_2470 with
      | UNIV (u,t) ->
          let x =
            let uu____2476 = FStar_Options.hide_uvar_nums ()  in
            if uu____2476
            then "?"
            else
              (let uu____2483 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____2483 FStar_Util.string_of_int)
             in
          let uu____2487 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____2487
      | TERM (u,t) ->
          let x =
            let uu____2494 = FStar_Options.hide_uvar_nums ()  in
            if uu____2494
            then "?"
            else
              (let uu____2501 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____2501 FStar_Util.string_of_int)
             in
          let uu____2505 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____2505
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____2524 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____2524 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____2545 =
      let uu____2549 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____2549
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____2545 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____2568 .
    (FStar_Syntax_Syntax.term * 'Auu____2568) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____2587 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____2608  ->
              match uu____2608 with
              | (x,uu____2615) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____2587 (FStar_String.concat " ")
  
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
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____2658 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____2658
         then
           let uu____2663 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____2663
         else ());
        Failed (prob, reason)
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_2674  ->
    match uu___3_2674 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____2680 .
    'Auu____2680 FStar_TypeChecker_Common.problem ->
      'Auu____2680 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___217_2692 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___217_2692.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___217_2692.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___217_2692.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___217_2692.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___217_2692.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___217_2692.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___217_2692.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____2700 .
    'Auu____2700 FStar_TypeChecker_Common.problem ->
      'Auu____2700 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_2720  ->
    match uu___4_2720 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _2726  -> FStar_TypeChecker_Common.TProb _2726)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _2732  -> FStar_TypeChecker_Common.CProb _2732)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_2738  ->
    match uu___5_2738 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___229_2744 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___229_2744.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___229_2744.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___229_2744.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___229_2744.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___229_2744.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___229_2744.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___229_2744.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___229_2744.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___229_2744.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___233_2752 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___233_2752.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___233_2752.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___233_2752.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___233_2752.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___233_2752.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___233_2752.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___233_2752.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___233_2752.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___233_2752.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_2765  ->
      match uu___6_2765 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_2772  ->
    match uu___7_2772 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_2785  ->
    match uu___8_2785 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_2800  ->
    match uu___9_2800 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_2815  ->
    match uu___10_2815 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_2829  ->
    match uu___11_2829 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_2843  ->
    match uu___12_2843 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_2855  ->
    match uu___13_2855 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____2871 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____2871) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____2901 =
          let uu____2903 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2903  in
        if uu____2901
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____2940)::bs ->
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
          let uu____2987 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____3011 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____3011]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____2987
      | FStar_TypeChecker_Common.CProb p ->
          let uu____3039 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____3063 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____3063]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____3039
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____3110 =
          let uu____3112 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____3112  in
        if uu____3110
        then ()
        else
          (let uu____3117 =
             let uu____3120 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____3120
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____3117 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____3169 =
          let uu____3171 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____3171  in
        if uu____3169
        then ()
        else
          (let uu____3176 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____3176)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____3196 =
        let uu____3198 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____3198  in
      if uu____3196
      then ()
      else
        (let msgf m =
           let uu____3212 =
             let uu____3214 =
               let uu____3216 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____3216 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____3214  in
           Prims.op_Hat msg uu____3212  in
         (let uu____3221 = msgf "scope"  in
          let uu____3224 = p_scope prob  in
          def_scope_wf uu____3221 (p_loc prob) uu____3224);
         (let uu____3236 = msgf "guard"  in
          def_check_scoped uu____3236 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____3243 = msgf "lhs"  in
                def_check_scoped uu____3243 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____3246 = msgf "rhs"  in
                def_check_scoped uu____3246 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____3253 = msgf "lhs"  in
                def_check_scoped_comp uu____3253 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____3256 = msgf "rhs"  in
                def_check_scoped_comp uu____3256 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___326_3277 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___326_3277.wl_deferred);
          ctr = (uu___326_3277.ctr);
          defer_ok = (uu___326_3277.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___326_3277.umax_heuristic_ok);
          tcenv = (uu___326_3277.tcenv);
          wl_implicits = (uu___326_3277.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____3285 .
    FStar_TypeChecker_Env.env ->
      ('Auu____3285 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___330_3308 = empty_worklist env  in
      let uu____3309 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____3309;
        wl_deferred = (uu___330_3308.wl_deferred);
        ctr = (uu___330_3308.ctr);
        defer_ok = (uu___330_3308.defer_ok);
        smt_ok = (uu___330_3308.smt_ok);
        umax_heuristic_ok = (uu___330_3308.umax_heuristic_ok);
        tcenv = (uu___330_3308.tcenv);
        wl_implicits = (uu___330_3308.wl_implicits)
      }
  
let (defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___335_3332 = wl  in
        {
          attempting = (uu___335_3332.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___335_3332.ctr);
          defer_ok = (uu___335_3332.defer_ok);
          smt_ok = (uu___335_3332.smt_ok);
          umax_heuristic_ok = (uu___335_3332.umax_heuristic_ok);
          tcenv = (uu___335_3332.tcenv);
          wl_implicits = (uu___335_3332.wl_implicits)
        }
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___340_3360 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___340_3360.wl_deferred);
         ctr = (uu___340_3360.ctr);
         defer_ok = (uu___340_3360.defer_ok);
         smt_ok = (uu___340_3360.smt_ok);
         umax_heuristic_ok = (uu___340_3360.umax_heuristic_ok);
         tcenv = (uu___340_3360.tcenv);
         wl_implicits = (uu___340_3360.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____3374 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____3374 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____3408 = FStar_Syntax_Util.type_u ()  in
            match uu____3408 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____3420 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____3420 with
                 | (uu____3438,tt,wl1) ->
                     let uu____3441 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____3441, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_3447  ->
    match uu___14_3447 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _3453  -> FStar_TypeChecker_Common.TProb _3453) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _3459  -> FStar_TypeChecker_Common.CProb _3459) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____3467 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____3467 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____3487  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____3529 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____3529 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____3529 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____3529 FStar_TypeChecker_Common.problem *
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
                        let uu____3616 =
                          let uu____3625 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3625]  in
                        FStar_List.append scope uu____3616
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____3668 =
                      let uu____3671 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____3671  in
                    FStar_List.append uu____3668
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____3690 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____3690 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____3716 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3716;
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
                  (let uu____3790 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____3790 with
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
                  (let uu____3878 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____3878 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____3916 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____3916 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____3916 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____3916 FStar_TypeChecker_Common.problem *
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
                          let uu____3984 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3984]  in
                        let uu____4003 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____4003
                     in
                  let uu____4006 =
                    let uu____4013 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___423_4024 = wl  in
                       {
                         attempting = (uu___423_4024.attempting);
                         wl_deferred = (uu___423_4024.wl_deferred);
                         ctr = (uu___423_4024.ctr);
                         defer_ok = (uu___423_4024.defer_ok);
                         smt_ok = (uu___423_4024.smt_ok);
                         umax_heuristic_ok =
                           (uu___423_4024.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___423_4024.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____4013
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____4006 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____4042 =
                              let uu____4047 =
                                let uu____4048 =
                                  let uu____4057 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____4057
                                   in
                                [uu____4048]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____4047  in
                            uu____4042 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____4085 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____4085;
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
                let uu____4133 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____4133;
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
  'Auu____4148 .
    worklist ->
      'Auu____4148 FStar_TypeChecker_Common.problem ->
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
              let uu____4181 =
                let uu____4184 =
                  let uu____4185 =
                    let uu____4192 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____4192)  in
                  FStar_Syntax_Syntax.NT uu____4185  in
                [uu____4184]  in
              FStar_Syntax_Subst.subst uu____4181 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____4216 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____4216
        then
          let uu____4224 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____4227 = prob_to_string env d  in
          let uu____4229 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____4224 uu____4227 uu____4229 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____4245 -> failwith "impossible"  in
           let uu____4248 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____4264 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____4266 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____4264, uu____4266)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____4273 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____4275 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____4273, uu____4275)
              in
           match uu____4248 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_4303  ->
            match uu___15_4303 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____4315 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____4319 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____4319 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_4350  ->
           match uu___16_4350 with
           | UNIV uu____4353 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____4360 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____4360
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
        (fun uu___17_4388  ->
           match uu___17_4388 with
           | UNIV (u',t) ->
               let uu____4393 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____4393
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____4400 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____4412 =
        let uu____4413 =
          let uu____4414 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____4414
           in
        FStar_Syntax_Subst.compress uu____4413  in
      FStar_All.pipe_right uu____4412 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____4426 =
        let uu____4427 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____4427  in
      FStar_All.pipe_right uu____4426 FStar_Syntax_Util.unlazy_emb
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4435 = FStar_Syntax_Util.head_and_args t  in
    match uu____4435 with
    | (h,uu____4454) ->
        let uu____4479 =
          let uu____4480 = FStar_Syntax_Subst.compress h  in
          uu____4480.FStar_Syntax_Syntax.n  in
        (match uu____4479 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____4485 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____4498 = should_strongly_reduce t  in
      if uu____4498
      then
        let uu____4501 =
          let uu____4502 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Reify;
              FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant] env t
             in
          FStar_Syntax_Subst.compress uu____4502  in
        FStar_All.pipe_right uu____4501 FStar_Syntax_Util.unlazy_emb
      else whnf' env t
  
let norm_arg :
  'Auu____4512 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____4512) ->
        (FStar_Syntax_Syntax.term * 'Auu____4512)
  =
  fun env  ->
    fun t  ->
      let uu____4535 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____4535, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____4587  ->
              match uu____4587 with
              | (x,imp) ->
                  let uu____4606 =
                    let uu___520_4607 = x  in
                    let uu____4608 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___520_4607.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___520_4607.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____4608
                    }  in
                  (uu____4606, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____4632 = aux u3  in FStar_Syntax_Syntax.U_succ uu____4632
        | FStar_Syntax_Syntax.U_max us ->
            let uu____4636 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____4636
        | uu____4639 -> u2  in
      let uu____4640 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____4640
  
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
          FStar_TypeChecker_Normalize.normalize_refinement steps env1 t  in
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____4761 = norm_refinement env t12  in
                 match uu____4761 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____4776;
                     FStar_Syntax_Syntax.vars = uu____4777;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____4801 =
                       let uu____4803 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____4805 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____4803 uu____4805
                        in
                     failwith uu____4801)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____4821 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____4821
          | FStar_Syntax_Syntax.Tm_uinst uu____4822 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4859 =
                   let uu____4860 = FStar_Syntax_Subst.compress t1'  in
                   uu____4860.FStar_Syntax_Syntax.n  in
                 match uu____4859 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4875 -> aux true t1'
                 | uu____4883 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____4898 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4929 =
                   let uu____4930 = FStar_Syntax_Subst.compress t1'  in
                   uu____4930.FStar_Syntax_Syntax.n  in
                 match uu____4929 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4945 -> aux true t1'
                 | uu____4953 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4968 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____5015 =
                   let uu____5016 = FStar_Syntax_Subst.compress t1'  in
                   uu____5016.FStar_Syntax_Syntax.n  in
                 match uu____5015 with
                 | FStar_Syntax_Syntax.Tm_refine uu____5031 -> aux true t1'
                 | uu____5039 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____5054 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____5069 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____5084 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____5099 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____5114 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____5143 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____5176 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____5197 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____5224 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____5252 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____5289 ->
              let uu____5296 =
                let uu____5298 = FStar_Syntax_Print.term_to_string t12  in
                let uu____5300 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____5298 uu____5300
                 in
              failwith uu____5296
          | FStar_Syntax_Syntax.Tm_ascribed uu____5315 ->
              let uu____5342 =
                let uu____5344 = FStar_Syntax_Print.term_to_string t12  in
                let uu____5346 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____5344 uu____5346
                 in
              failwith uu____5342
          | FStar_Syntax_Syntax.Tm_delayed uu____5361 ->
              let uu____5384 =
                let uu____5386 = FStar_Syntax_Print.term_to_string t12  in
                let uu____5388 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____5386 uu____5388
                 in
              failwith uu____5384
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____5403 =
                let uu____5405 = FStar_Syntax_Print.term_to_string t12  in
                let uu____5407 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____5405 uu____5407
                 in
              failwith uu____5403
           in
        let uu____5422 = whnf env t1  in aux false uu____5422
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        FStar_TypeChecker_Normalize.normalize_refinement steps env t0
  
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____5483 = base_and_refinement env t  in
      FStar_All.pipe_right uu____5483 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____5524 = FStar_Syntax_Syntax.null_bv t  in
    (uu____5524, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____5551 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____5551 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____5611  ->
    match uu____5611 with
    | (t_base,refopt) ->
        let uu____5642 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____5642 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____5684 =
      let uu____5688 =
        let uu____5691 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____5718  ->
                  match uu____5718 with | (uu____5727,uu____5728,x) -> x))
           in
        FStar_List.append wl.attempting uu____5691  in
      FStar_List.map (wl_prob_to_string wl) uu____5688  in
    FStar_All.pipe_right uu____5684 (FStar_String.concat "\n\t")
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
    FStar_Syntax_Syntax.args)
let flex_t_to_string :
  'Auu____5751 .
    ('Auu____5751 * FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.args)
      -> Prims.string
  =
  fun uu____5763  ->
    match uu____5763 with
    | (uu____5770,c,args) ->
        let uu____5773 = print_ctx_uvar c  in
        let uu____5775 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____5773 uu____5775
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____5785 = FStar_Syntax_Util.head_and_args t  in
    match uu____5785 with
    | (head1,_args) ->
        let uu____5829 =
          let uu____5830 = FStar_Syntax_Subst.compress head1  in
          uu____5830.FStar_Syntax_Syntax.n  in
        (match uu____5829 with
         | FStar_Syntax_Syntax.Tm_uvar uu____5834 -> true
         | uu____5848 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____5856 = FStar_Syntax_Util.head_and_args t  in
    match uu____5856 with
    | (head1,_args) ->
        let uu____5899 =
          let uu____5900 = FStar_Syntax_Subst.compress head1  in
          uu____5900.FStar_Syntax_Syntax.n  in
        (match uu____5899 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____5904) -> u
         | uu____5921 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5946 = FStar_Syntax_Util.head_and_args t  in
      match uu____5946 with
      | (head1,args) ->
          let uu____5993 =
            let uu____5994 = FStar_Syntax_Subst.compress head1  in
            uu____5994.FStar_Syntax_Syntax.n  in
          (match uu____5993 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____6002)) ->
               ((t, uv, args), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____6035 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_6060  ->
                         match uu___18_6060 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____6065 =
                               let uu____6066 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____6066.FStar_Syntax_Syntax.n  in
                             (match uu____6065 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____6071 -> false)
                         | uu____6073 -> true))
                  in
               (match uu____6035 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____6098 =
                        FStar_List.collect
                          (fun uu___19_6110  ->
                             match uu___19_6110 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____6114 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____6114]
                             | uu____6115 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____6098 FStar_List.rev  in
                    let uu____6138 =
                      let uu____6145 =
                        let uu____6154 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_6176  ->
                                  match uu___20_6176 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____6180 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____6180]
                                  | uu____6181 -> []))
                           in
                        FStar_All.pipe_right uu____6154 FStar_List.rev  in
                      let uu____6204 =
                        let uu____6207 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____6207  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____6145 uu____6204
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____6138 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____6243  ->
                                match uu____6243 with
                                | (x,i) ->
                                    let uu____6262 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____6262, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____6293  ->
                                match uu____6293 with
                                | (a,i) ->
                                    let uu____6312 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____6312, i)) args_sol
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
           | uu____6334 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____6356 =
          let uu____6379 =
            let uu____6380 = FStar_Syntax_Subst.compress k  in
            uu____6380.FStar_Syntax_Syntax.n  in
          match uu____6379 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____6462 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____6462)
              else
                (let uu____6497 = FStar_Syntax_Util.abs_formals t  in
                 match uu____6497 with
                 | (ys',t1,uu____6530) ->
                     let uu____6535 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____6535))
          | uu____6574 ->
              let uu____6575 =
                let uu____6580 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____6580)  in
              ((ys, t), uu____6575)
           in
        match uu____6356 with
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
                 let uu____6675 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____6675 c  in
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
               (let uu____6753 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____6753
                then
                  let uu____6758 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____6760 = print_ctx_uvar uv  in
                  let uu____6762 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____6758 uu____6760 uu____6762
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____6771 =
                   let uu____6773 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____6773  in
                 let uu____6776 =
                   let uu____6779 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____6779
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____6771 uu____6776 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____6812 =
               let uu____6813 =
                 let uu____6815 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____6817 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____6815 uu____6817
                  in
               failwith uu____6813  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6883  ->
                       match uu____6883 with
                       | (a,i) ->
                           let uu____6904 =
                             let uu____6905 = FStar_Syntax_Subst.compress a
                                in
                             uu____6905.FStar_Syntax_Syntax.n  in
                           (match uu____6904 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6931 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6941 =
                 let uu____6943 = is_flex g  in Prims.op_Negation uu____6943
                  in
               if uu____6941
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6952 = destruct_flex_t g wl  in
                  match uu____6952 with
                  | ((uu____6957,uv1,args),wl1) ->
                      ((let uu____6962 = args_as_binders args  in
                        assign_solution uu____6962 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___772_6964 = wl1  in
              {
                attempting = (uu___772_6964.attempting);
                wl_deferred = (uu___772_6964.wl_deferred);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___772_6964.defer_ok);
                smt_ok = (uu___772_6964.smt_ok);
                umax_heuristic_ok = (uu___772_6964.umax_heuristic_ok);
                tcenv = (uu___772_6964.tcenv);
                wl_implicits = (uu___772_6964.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6989 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6989
         then
           let uu____6994 = FStar_Util.string_of_int pid  in
           let uu____6996 =
             let uu____6998 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6998 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6994 uu____6996
         else ());
        commit sol;
        (let uu___780_7012 = wl  in
         {
           attempting = (uu___780_7012.attempting);
           wl_deferred = (uu___780_7012.wl_deferred);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___780_7012.defer_ok);
           smt_ok = (uu___780_7012.smt_ok);
           umax_heuristic_ok = (uu___780_7012.umax_heuristic_ok);
           tcenv = (uu___780_7012.tcenv);
           wl_implicits = (uu___780_7012.wl_implicits)
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
          (let conj_guard1 t g =
             match (t, g) with
             | (uu____7078,FStar_TypeChecker_Common.Trivial ) -> t
             | (FStar_Pervasives_Native.None
                ,FStar_TypeChecker_Common.NonTrivial f) ->
                 FStar_Pervasives_Native.Some f
             | (FStar_Pervasives_Native.Some
                t1,FStar_TypeChecker_Common.NonTrivial f) ->
                 let uu____7106 = FStar_Syntax_Util.mk_conj t1 f  in
                 FStar_Pervasives_Native.Some uu____7106
              in
           (let uu____7112 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                (FStar_Options.Other "Rel")
               in
            if uu____7112
            then
              let uu____7117 =
                FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
              let uu____7121 =
                let uu____7123 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                   in
                FStar_All.pipe_right uu____7123 (FStar_String.concat ", ")
                 in
              FStar_Util.print2 "Solving %s: with %s\n" uu____7117 uu____7121
            else ());
           solve_prob' false prob logical_guard uvis wl)
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____7158 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____7158 FStar_Util.set_elements  in
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
      let uu____7198 = occurs uk t  in
      match uu____7198 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____7237 =
                 let uu____7239 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____7241 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____7239 uu____7241
                  in
               FStar_Pervasives_Native.Some uu____7237)
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
            let uu____7361 = maximal_prefix bs_tail bs'_tail  in
            (match uu____7361 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____7412 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____7469  ->
             match uu____7469 with
             | (x,uu____7481) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____7499 = FStar_List.last bs  in
      match uu____7499 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____7523) ->
          let uu____7534 =
            FStar_Util.prefix_until
              (fun uu___21_7549  ->
                 match uu___21_7549 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____7552 -> false) g
             in
          (match uu____7534 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____7566,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____7603 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____7603 with
        | (pfx,uu____7613) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____7625 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____7625 with
             | (uu____7633,src',wl1) ->
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
                 | uu____7747 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____7748 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____7812  ->
                  fun uu____7813  ->
                    match (uu____7812, uu____7813) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____7916 =
                          let uu____7918 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____7918
                           in
                        if uu____7916
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7952 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____7952
                           then
                             let uu____7969 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7969)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____7748 with | (isect,uu____8019) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____8055 'Auu____8056 .
    (FStar_Syntax_Syntax.bv * 'Auu____8055) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____8056) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____8114  ->
              fun uu____8115  ->
                match (uu____8114, uu____8115) with
                | ((a,uu____8134),(b,uu____8136)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____8152 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____8152) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____8183  ->
           match uu____8183 with
           | (y,uu____8190) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____8200 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____8200) Prims.list ->
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
                   let uu____8362 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____8362
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____8395 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____8447 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____8491 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____8512 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_8520  ->
    match uu___22_8520 with
    | MisMatch (d1,d2) ->
        let uu____8532 =
          let uu____8534 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____8536 =
            let uu____8538 =
              let uu____8540 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____8540 ")"  in
            Prims.op_Hat ") (" uu____8538  in
          Prims.op_Hat uu____8534 uu____8536  in
        Prims.op_Hat "MisMatch (" uu____8532
    | HeadMatch u ->
        let uu____8547 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____8547
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_8556  ->
    match uu___23_8556 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____8573 -> HeadMatch false
  
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
          let uu____8595 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____8595 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____8606 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____8630 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____8640 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____8667 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____8667
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____8668 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____8669 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____8670 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____8683 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____8697 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____8721) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____8727,uu____8728) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____8770) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____8795;
             FStar_Syntax_Syntax.index = uu____8796;
             FStar_Syntax_Syntax.sort = t2;_},uu____8798)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____8806 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____8807 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____8808 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____8823 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____8830 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____8850 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____8850
  
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
           { FStar_Syntax_Syntax.blob = uu____8869;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____8870;
             FStar_Syntax_Syntax.ltyp = uu____8871;
             FStar_Syntax_Syntax.rng = uu____8872;_},uu____8873)
            ->
            let uu____8884 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____8884 t21
        | (uu____8885,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____8886;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____8887;
             FStar_Syntax_Syntax.ltyp = uu____8888;
             FStar_Syntax_Syntax.rng = uu____8889;_})
            ->
            let uu____8900 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____8900
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____8912 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____8912
            then FullMatch
            else
              (let uu____8917 =
                 let uu____8926 =
                   let uu____8929 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____8929  in
                 let uu____8930 =
                   let uu____8933 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____8933  in
                 (uu____8926, uu____8930)  in
               MisMatch uu____8917)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____8939),FStar_Syntax_Syntax.Tm_uinst (g,uu____8941)) ->
            let uu____8950 = head_matches env f g  in
            FStar_All.pipe_right uu____8950 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____8951) -> HeadMatch true
        | (uu____8953,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8957 = FStar_Const.eq_const c d  in
            if uu____8957
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8967),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8969)) ->
            let uu____9002 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____9002
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____9012),FStar_Syntax_Syntax.Tm_refine (y,uu____9014)) ->
            let uu____9023 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____9023 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____9025),uu____9026) ->
            let uu____9031 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____9031 head_match
        | (uu____9032,FStar_Syntax_Syntax.Tm_refine (x,uu____9034)) ->
            let uu____9039 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____9039 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____9040,FStar_Syntax_Syntax.Tm_type
           uu____9041) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____9043,FStar_Syntax_Syntax.Tm_arrow uu____9044) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____9075),FStar_Syntax_Syntax.Tm_app (head',uu____9077))
            ->
            let uu____9126 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____9126 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____9128),uu____9129) ->
            let uu____9154 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____9154 head_match
        | (uu____9155,FStar_Syntax_Syntax.Tm_app (head1,uu____9157)) ->
            let uu____9182 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____9182 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____9183,FStar_Syntax_Syntax.Tm_let
           uu____9184) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____9212,FStar_Syntax_Syntax.Tm_match uu____9213) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____9259,FStar_Syntax_Syntax.Tm_abs
           uu____9260) -> HeadMatch true
        | uu____9298 ->
            let uu____9303 =
              let uu____9312 = delta_depth_of_term env t11  in
              let uu____9315 = delta_depth_of_term env t21  in
              (uu____9312, uu____9315)  in
            MisMatch uu____9303
  
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
              let uu____9384 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____9384  in
            (let uu____9386 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____9386
             then
               let uu____9391 = FStar_Syntax_Print.term_to_string t  in
               let uu____9393 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____9391 uu____9393
             else ());
            (let uu____9398 =
               let uu____9399 = FStar_Syntax_Util.un_uinst head1  in
               uu____9399.FStar_Syntax_Syntax.n  in
             match uu____9398 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____9405 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____9405 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____9419 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____9419
                        then
                          let uu____9424 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____9424
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____9429 ->
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
                        FStar_TypeChecker_Normalize.normalize steps env t  in
                      let uu____9446 =
                        let uu____9448 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____9448 = FStar_Syntax_Util.Equal  in
                      if uu____9446
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____9455 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____9455
                          then
                            let uu____9460 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____9462 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____9460
                              uu____9462
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____9467 -> FStar_Pervasives_Native.None)
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
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____9619 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____9619
             then
               let uu____9624 = FStar_Syntax_Print.term_to_string t11  in
               let uu____9626 = FStar_Syntax_Print.term_to_string t21  in
               let uu____9628 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____9624
                 uu____9626 uu____9628
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____9656 =
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
               match uu____9656 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____9704 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____9704 with
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
                  uu____9742),uu____9743)
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____9764 =
                      let uu____9773 = maybe_inline t11  in
                      let uu____9776 = maybe_inline t21  in
                      (uu____9773, uu____9776)  in
                    match uu____9764 with
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
                 (uu____9819,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____9820))
                 ->
                 if Prims.op_Negation retry
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____9841 =
                      let uu____9850 = maybe_inline t11  in
                      let uu____9853 = maybe_inline t21  in
                      (uu____9850, uu____9853)  in
                    match uu____9841 with
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
             | MisMatch uu____9908 -> fail1 n_delta r t11 t21
             | uu____9917 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____9932 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____9932
           then
             let uu____9937 = FStar_Syntax_Print.term_to_string t1  in
             let uu____9939 = FStar_Syntax_Print.term_to_string t2  in
             let uu____9941 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____9949 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9966 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9966
                    (fun uu____10001  ->
                       match uu____10001 with
                       | (t11,t21) ->
                           let uu____10009 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____10011 =
                             let uu____10013 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____10013  in
                           Prims.op_Hat uu____10009 uu____10011))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____9937 uu____9939 uu____9941 uu____9949
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____10030 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____10030 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_10045  ->
    match uu___24_10045 with
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
      let uu___1284_10094 = p  in
      let uu____10097 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____10098 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1284_10094.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____10097;
        FStar_TypeChecker_Common.relation =
          (uu___1284_10094.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____10098;
        FStar_TypeChecker_Common.element =
          (uu___1284_10094.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1284_10094.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1284_10094.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1284_10094.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1284_10094.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1284_10094.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____10113 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____10113
            (fun _10118  -> FStar_TypeChecker_Common.TProb _10118)
      | FStar_TypeChecker_Common.CProb uu____10119 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____10142 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____10142 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____10150 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____10150 with
           | (lh,lhs_args) ->
               let uu____10197 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____10197 with
                | (rh,rhs_args) ->
                    let uu____10244 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____10257,FStar_Syntax_Syntax.Tm_uvar uu____10258)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____10347 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____10374,uu____10375)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____10390,FStar_Syntax_Syntax.Tm_uvar uu____10391)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____10406,FStar_Syntax_Syntax.Tm_arrow
                         uu____10407) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1335_10437 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1335_10437.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1335_10437.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1335_10437.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1335_10437.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1335_10437.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1335_10437.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1335_10437.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1335_10437.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1335_10437.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____10440,FStar_Syntax_Syntax.Tm_type uu____10441)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1335_10457 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1335_10457.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1335_10457.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1335_10457.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1335_10457.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1335_10457.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1335_10457.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1335_10457.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1335_10457.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1335_10457.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____10460,FStar_Syntax_Syntax.Tm_uvar uu____10461)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1335_10477 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1335_10477.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1335_10477.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1335_10477.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1335_10477.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1335_10477.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1335_10477.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1335_10477.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1335_10477.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1335_10477.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____10480,FStar_Syntax_Syntax.Tm_uvar uu____10481)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____10496,uu____10497)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____10512,FStar_Syntax_Syntax.Tm_uvar uu____10513)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____10528,uu____10529) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____10244 with
                     | (rank,tp1) ->
                         let uu____10542 =
                           FStar_All.pipe_right
                             (let uu___1355_10546 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1355_10546.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1355_10546.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1355_10546.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1355_10546.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1355_10546.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1355_10546.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1355_10546.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1355_10546.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1355_10546.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _10549  ->
                                FStar_TypeChecker_Common.TProb _10549)
                            in
                         (rank, uu____10542))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____10553 =
            FStar_All.pipe_right
              (let uu___1359_10557 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1359_10557.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1359_10557.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1359_10557.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1359_10557.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1359_10557.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1359_10557.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1359_10557.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1359_10557.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1359_10557.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _10560  -> FStar_TypeChecker_Common.CProb _10560)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____10553)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____10620 probs =
      match uu____10620 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____10701 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____10722 = rank wl.tcenv hd1  in
               (match uu____10722 with
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
                      (let uu____10783 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____10788 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____10788)
                          in
                       if uu____10783
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
          let uu____10861 = FStar_Syntax_Util.head_and_args t  in
          match uu____10861 with
          | (hd1,uu____10880) ->
              let uu____10905 =
                let uu____10906 = FStar_Syntax_Subst.compress hd1  in
                uu____10906.FStar_Syntax_Syntax.n  in
              (match uu____10905 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____10911) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____10946  ->
                           match uu____10946 with
                           | (y,uu____10955) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10978  ->
                                       match uu____10978 with
                                       | (x,uu____10987) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10992 -> false)
           in
        let uu____10994 = rank tcenv p  in
        match uu____10994 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____11003 -> true
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
  | UFailed of Prims.string 
let (uu___is_UDeferred : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____11040 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____11059 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____11079 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> Prims.string) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
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
                        let uu____11141 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____11141 with
                        | (k,uu____11149) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____11162 -> false)))
            | uu____11164 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____11216 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____11224 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____11224 = Prims.int_zero))
                           in
                        if uu____11216 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____11245 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____11253 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____11253 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____11245)
               in
            let uu____11257 = filter1 u12  in
            let uu____11260 = filter1 u22  in (uu____11257, uu____11260)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then UFailed "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____11295 = filter_out_common_univs us1 us2  in
                   (match uu____11295 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____11355 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____11355 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____11358 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          (let uu____11369 =
                             let uu____11371 =
                               FStar_Syntax_Print.univ_to_string u12  in
                             let uu____11373 =
                               FStar_Syntax_Print.univ_to_string u22  in
                             FStar_Util.format2
                               "Unable to unify universes: %s and %s"
                               uu____11371 uu____11373
                              in
                           UFailed uu____11369))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____11399 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____11399 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____11425 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____11425 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____11428 ->
                   let uu____11433 =
                     let uu____11435 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____11437 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format3
                       "Unable to unify universes: %s and %s (%s)"
                       uu____11435 uu____11437 msg
                      in
                   UFailed uu____11433)
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____11440,uu____11441) ->
              let uu____11443 =
                let uu____11445 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____11447 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____11445 uu____11447
                 in
              failwith uu____11443
          | (FStar_Syntax_Syntax.U_unknown ,uu____11450) ->
              let uu____11451 =
                let uu____11453 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____11455 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____11453 uu____11455
                 in
              failwith uu____11451
          | (uu____11458,FStar_Syntax_Syntax.U_bvar uu____11459) ->
              let uu____11461 =
                let uu____11463 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____11465 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____11463 uu____11465
                 in
              failwith uu____11461
          | (uu____11468,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____11469 =
                let uu____11471 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____11473 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____11471 uu____11473
                 in
              failwith uu____11469
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____11503 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____11503
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____11520 = occurs_univ v1 u3  in
              if uu____11520
              then
                let uu____11523 =
                  let uu____11525 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____11527 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____11525 uu____11527
                   in
                try_umax_components u11 u21 uu____11523
              else
                (let uu____11532 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____11532)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____11544 = occurs_univ v1 u3  in
              if uu____11544
              then
                let uu____11547 =
                  let uu____11549 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____11551 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____11549 uu____11551
                   in
                try_umax_components u11 u21 uu____11547
              else
                (let uu____11556 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____11556)
          | (FStar_Syntax_Syntax.U_max uu____11557,uu____11558) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____11566 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____11566
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____11572,FStar_Syntax_Syntax.U_max uu____11573) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____11581 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____11581
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____11587,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____11589,FStar_Syntax_Syntax.U_name uu____11590) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____11592) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____11594) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____11596,FStar_Syntax_Syntax.U_succ uu____11597) ->
              UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____11599,FStar_Syntax_Syntax.U_zero ) ->
              UFailed "Incompatible universes"
  
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
      let uu____11706 = bc1  in
      match uu____11706 with
      | (bs1,mk_cod1) ->
          let uu____11750 = bc2  in
          (match uu____11750 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____11861 = aux xs ys  in
                     (match uu____11861 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11944 =
                       let uu____11951 = mk_cod1 xs  in ([], uu____11951)  in
                     let uu____11954 =
                       let uu____11961 = mk_cod2 ys  in ([], uu____11961)  in
                     (uu____11944, uu____11954)
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
                  let uu____12030 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____12030 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____12033 =
                    let uu____12034 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____12034 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____12033
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____12039 = has_type_guard t1 t2  in (uu____12039, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____12040 = has_type_guard t2 t1  in (uu____12040, wl)
  
let is_flex_pat :
  'Auu____12050 'Auu____12051 'Auu____12052 .
    ('Auu____12050 * 'Auu____12051 * 'Auu____12052 Prims.list) -> Prims.bool
  =
  fun uu___25_12066  ->
    match uu___25_12066 with
    | (uu____12075,uu____12076,[]) -> true
    | uu____12080 -> false
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____12113 = f  in
      match uu____12113 with
      | (uu____12120,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____12121;
                       FStar_Syntax_Syntax.ctx_uvar_gamma = uu____12122;
                       FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                       FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                       FStar_Syntax_Syntax.ctx_uvar_reason = uu____12125;
                       FStar_Syntax_Syntax.ctx_uvar_should_check =
                         uu____12126;
                       FStar_Syntax_Syntax.ctx_uvar_range = uu____12127;
                       FStar_Syntax_Syntax.ctx_uvar_meta = uu____12128;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____12198  ->
                 match uu____12198 with
                 | (y,uu____12207) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____12361 =
                  let uu____12376 =
                    let uu____12379 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____12379  in
                  ((FStar_List.rev pat_binders), uu____12376)  in
                FStar_Pervasives_Native.Some uu____12361
            | (uu____12412,[]) ->
                let uu____12443 =
                  let uu____12458 =
                    let uu____12461 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____12461  in
                  ((FStar_List.rev pat_binders), uu____12458)  in
                FStar_Pervasives_Native.Some uu____12443
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____12552 =
                  let uu____12553 = FStar_Syntax_Subst.compress a  in
                  uu____12553.FStar_Syntax_Syntax.n  in
                (match uu____12552 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____12573 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____12573
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1683_12603 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1683_12603.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1683_12603.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____12607 =
                            let uu____12608 =
                              let uu____12615 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____12615)  in
                            FStar_Syntax_Syntax.NT uu____12608  in
                          [uu____12607]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1689_12631 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1689_12631.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1689_12631.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____12632 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____12672 =
                  let uu____12687 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____12687  in
                (match uu____12672 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____12762 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____12795 ->
               let uu____12796 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____12796 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____13118 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____13118
       then
         let uu____13123 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____13123
       else ());
      (let uu____13128 = next_prob probs  in
       match uu____13128 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1714_13155 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1714_13155.wl_deferred);
               ctr = (uu___1714_13155.ctr);
               defer_ok = (uu___1714_13155.defer_ok);
               smt_ok = (uu___1714_13155.smt_ok);
               umax_heuristic_ok = (uu___1714_13155.umax_heuristic_ok);
               tcenv = (uu___1714_13155.tcenv);
               wl_implicits = (uu___1714_13155.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____13164 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____13164
                 then
                   let uu____13167 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____13167
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
                       solve env
                         (defer "deferring flex_rigid or flex_flex subtyping"
                            hd1 probs1)
                     else
                       if rank1 = FStar_TypeChecker_Common.Flex_flex
                       then
                         solve_t env
                           (let uu___1726_13179 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1726_13179.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1726_13179.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1726_13179.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1726_13179.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1726_13179.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1726_13179.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1726_13179.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1726_13179.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1726_13179.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] -> Success ([], (probs.wl_implicits))
            | uu____13205 ->
                let uu____13216 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____13287  ->
                          match uu____13287 with
                          | (c,uu____13298,uu____13299) -> c < probs.ctr))
                   in
                (match uu____13216 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____13354 =
                            let uu____13359 =
                              FStar_List.map
                                (fun uu____13377  ->
                                   match uu____13377 with
                                   | (uu____13391,x,y) -> (x, y))
                                probs.wl_deferred
                               in
                            (uu____13359, (probs.wl_implicits))  in
                          Success uu____13354
                      | uu____13399 ->
                          let uu____13410 =
                            let uu___1744_13411 = probs  in
                            let uu____13412 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____13435  ->
                                      match uu____13435 with
                                      | (uu____13444,uu____13445,y) -> y))
                               in
                            {
                              attempting = uu____13412;
                              wl_deferred = rest;
                              ctr = (uu___1744_13411.ctr);
                              defer_ok = (uu___1744_13411.defer_ok);
                              smt_ok = (uu___1744_13411.smt_ok);
                              umax_heuristic_ok =
                                (uu___1744_13411.umax_heuristic_ok);
                              tcenv = (uu___1744_13411.tcenv);
                              wl_implicits = (uu___1744_13411.wl_implicits)
                            }  in
                          solve env uu____13410))))

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
            let uu____13456 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____13456 with
            | USolved wl1 ->
                let uu____13458 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____13458
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

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
                  let uu____13512 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____13512 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____13515 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____13528;
                  FStar_Syntax_Syntax.vars = uu____13529;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____13532;
                  FStar_Syntax_Syntax.vars = uu____13533;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____13546,uu____13547) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____13555,FStar_Syntax_Syntax.Tm_uinst uu____13556) ->
                failwith "Impossible: expect head symbols to match"
            | uu____13564 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____13576 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____13576
              then
                let uu____13581 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____13581 msg
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
               let uu____13673 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____13673 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____13728 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13728
                then
                  let uu____13733 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____13735 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____13733 uu____13735
                else ());
               (let uu____13740 = head_matches_delta env1 wl2 t1 t2  in
                match uu____13740 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____13786 = eq_prob t1 t2 wl2  in
                         (match uu____13786 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13807 ->
                         let uu____13816 = eq_prob t1 t2 wl2  in
                         (match uu____13816 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13866 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13881 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13882 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13881, uu____13882)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13887 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13888 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13887, uu____13888)
                            in
                         (match uu____13866 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13919 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13919 with
                                | (t1_hd,t1_args) ->
                                    let uu____13964 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13964 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____14030 =
                                              let uu____14037 =
                                                let uu____14048 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____14048 :: t1_args  in
                                              let uu____14065 =
                                                let uu____14074 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____14074 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____14123  ->
                                                   fun uu____14124  ->
                                                     fun uu____14125  ->
                                                       match (uu____14123,
                                                               uu____14124,
                                                               uu____14125)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____14175),
                                                          (a2,uu____14177))
                                                           ->
                                                           let uu____14214 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____14214
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____14037
                                                uu____14065
                                               in
                                            match uu____14030 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1898_14240 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    ctr =
                                                      (uu___1898_14240.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1898_14240.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1898_14240.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14252 =
                                                  solve env1 wl'  in
                                                (match uu____14252 with
                                                 | Success (uu____14255,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      FStar_Pervasives_Native.Some
                                                        ((let uu___1907_14259
                                                            = wl4  in
                                                          {
                                                            attempting =
                                                              (uu___1907_14259.attempting);
                                                            wl_deferred =
                                                              (uu___1907_14259.wl_deferred);
                                                            ctr =
                                                              (uu___1907_14259.ctr);
                                                            defer_ok =
                                                              (uu___1907_14259.defer_ok);
                                                            smt_ok =
                                                              (uu___1907_14259.smt_ok);
                                                            umax_heuristic_ok
                                                              =
                                                              (uu___1907_14259.umax_heuristic_ok);
                                                            tcenv =
                                                              (uu___1907_14259.tcenv);
                                                            wl_implicits =
                                                              (FStar_List.append
                                                                 wl4.wl_implicits
                                                                 imps)
                                                          })))
                                                 | Failed uu____14260 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____14293 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____14293 with
                                | (t1_base,p1_opt) ->
                                    let uu____14329 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____14329 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____14428 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____14428
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
                                               let uu____14481 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____14481
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
                                               let uu____14513 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____14513
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
                                               let uu____14545 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____14545
                                           | uu____14548 -> t_base  in
                                         let uu____14565 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____14565 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____14579 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____14579, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____14586 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____14586 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____14622 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____14622 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____14658 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____14658
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
                              let uu____14682 = combine t11 t21 wl2  in
                              (match uu____14682 with
                               | (t12,ps,wl3) ->
                                   ((let uu____14715 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____14715
                                     then
                                       let uu____14720 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____14720
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____14762 ts1 =
               match uu____14762 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14825 = pairwise out t wl2  in
                        (match uu____14825 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14861 =
               let uu____14872 = FStar_List.hd ts  in (uu____14872, [], wl1)
                in
             let uu____14881 = FStar_List.tl ts  in
             aux uu____14861 uu____14881  in
           let uu____14888 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14888 with
           | (this_flex,this_rigid) ->
               let uu____14914 =
                 let uu____14915 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14915.FStar_Syntax_Syntax.n  in
               (match uu____14914 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14940 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14940
                    then
                      let uu____14943 = destruct_flex_t this_flex wl  in
                      (match uu____14943 with
                       | (flex,wl1) ->
                           let uu____14950 = quasi_pattern env flex  in
                           (match uu____14950 with
                            | FStar_Pervasives_Native.None  ->
                                giveup env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14969 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14969
                                  then
                                    let uu____14974 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14974
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14981 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2009_14984 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2009_14984.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2009_14984.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2009_14984.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2009_14984.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2009_14984.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2009_14984.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2009_14984.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2009_14984.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2009_14984.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14981)
                | uu____14985 ->
                    ((let uu____14987 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14987
                      then
                        let uu____14992 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14992
                      else ());
                     (let uu____14997 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14997 with
                      | (u,_args) ->
                          let uu____15040 =
                            let uu____15041 = FStar_Syntax_Subst.compress u
                               in
                            uu____15041.FStar_Syntax_Syntax.n  in
                          (match uu____15040 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____15069 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____15069 with
                                 | (u',uu____15088) ->
                                     let uu____15113 =
                                       let uu____15114 = whnf env u'  in
                                       uu____15114.FStar_Syntax_Syntax.n  in
                                     (match uu____15113 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____15136 -> false)
                                  in
                               let uu____15138 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_15161  ->
                                         match uu___26_15161 with
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
                                              | uu____15175 -> false)
                                         | uu____15179 -> false))
                                  in
                               (match uu____15138 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____15194 = whnf env this_rigid
                                         in
                                      let uu____15195 =
                                        FStar_List.collect
                                          (fun uu___27_15201  ->
                                             match uu___27_15201 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____15207 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____15207]
                                             | uu____15211 -> [])
                                          bounds_probs
                                         in
                                      uu____15194 :: uu____15195  in
                                    let uu____15212 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____15212 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____15245 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____15260 =
                                               let uu____15261 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____15261.FStar_Syntax_Syntax.n
                                                in
                                             match uu____15260 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____15273 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____15273)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____15284 -> bound  in
                                           let uu____15285 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____15285)  in
                                         (match uu____15245 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____15320 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____15320
                                                then
                                                  let wl'1 =
                                                    let uu___2069_15326 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2069_15326.wl_deferred);
                                                      ctr =
                                                        (uu___2069_15326.ctr);
                                                      defer_ok =
                                                        (uu___2069_15326.defer_ok);
                                                      smt_ok =
                                                        (uu___2069_15326.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2069_15326.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2069_15326.tcenv);
                                                      wl_implicits =
                                                        (uu___2069_15326.wl_implicits)
                                                    }  in
                                                  let uu____15327 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____15327
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____15333 =
                                                  solve_t env eq_prob
                                                    (let uu___2074_15335 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2074_15335.wl_deferred);
                                                       ctr =
                                                         (uu___2074_15335.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2074_15335.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2074_15335.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2074_15335.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____15333 with
                                                | Success (uu____15337,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2080_15340 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2080_15340.wl_deferred);
                                                        ctr =
                                                          (uu___2080_15340.ctr);
                                                        defer_ok =
                                                          (uu___2080_15340.defer_ok);
                                                        smt_ok =
                                                          (uu___2080_15340.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2080_15340.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2080_15340.tcenv);
                                                        wl_implicits =
                                                          (uu___2080_15340.wl_implicits)
                                                      }  in
                                                    let wl3 =
                                                      let uu___2083_15342 =
                                                        wl2  in
                                                      {
                                                        attempting =
                                                          (uu___2083_15342.attempting);
                                                        wl_deferred =
                                                          (uu___2083_15342.wl_deferred);
                                                        ctr =
                                                          (uu___2083_15342.ctr);
                                                        defer_ok =
                                                          (uu___2083_15342.defer_ok);
                                                        smt_ok =
                                                          (uu___2083_15342.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2083_15342.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2083_15342.tcenv);
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
                                                    let uu____15358 =
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
                                                    ((let uu____15372 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____15372
                                                      then
                                                        let uu____15377 =
                                                          let uu____15379 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15379
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____15377
                                                      else ());
                                                     (let uu____15392 =
                                                        let uu____15407 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____15407)
                                                         in
                                                      match uu____15392 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____15429))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____15455 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____15455
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
                                                                  let uu____15475
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____15475))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____15500 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____15500
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
                                                                    let uu____15520
                                                                    =
                                                                    let uu____15525
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____15525
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____15520
                                                                    [] wl2
                                                                     in
                                                                  let uu____15531
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____15531))))
                                                      | uu____15532 ->
                                                          giveup env
                                                            (Prims.op_Hat
                                                               "failed to solve sub-problems: "
                                                               msg) p)))))))
                           | uu____15548 when flip ->
                               let uu____15549 =
                                 let uu____15551 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____15553 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____15551 uu____15553
                                  in
                               failwith uu____15549
                           | uu____15556 ->
                               let uu____15557 =
                                 let uu____15559 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____15561 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____15559 uu____15561
                                  in
                               failwith uu____15557)))))

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
                      (fun uu____15597  ->
                         match uu____15597 with
                         | (x,i) ->
                             let uu____15616 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____15616, i)) bs_lhs
                     in
                  let uu____15619 = lhs  in
                  match uu____15619 with
                  | (uu____15620,u_lhs,uu____15622) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____15719 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____15729 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____15729, univ)
                             in
                          match uu____15719 with
                          | (k,univ) ->
                              let uu____15736 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____15736 with
                               | (uu____15753,u,wl3) ->
                                   let uu____15756 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____15756, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15782 =
                              let uu____15795 =
                                let uu____15806 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15806 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15857  ->
                                   fun uu____15858  ->
                                     match (uu____15857, uu____15858) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15959 =
                                           let uu____15966 =
                                             let uu____15969 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15969
                                              in
                                           copy_uvar u_lhs [] uu____15966 wl2
                                            in
                                         (match uu____15959 with
                                          | (uu____15998,t_a,wl3) ->
                                              let uu____16001 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____16001 with
                                               | (uu____16020,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15795
                                ([], wl1)
                               in
                            (match uu____15782 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2193_16076 = ct  in
                                   let uu____16077 =
                                     let uu____16080 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____16080
                                      in
                                   let uu____16095 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2193_16076.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2193_16076.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____16077;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____16095;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2193_16076.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2196_16113 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2196_16113.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2196_16113.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____16116 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____16116 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____16178 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____16178 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____16189 =
                                          let uu____16194 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16194)  in
                                        TERM uu____16189  in
                                      let uu____16195 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____16195 with
                                       | (sub_prob,wl3) ->
                                           let uu____16209 =
                                             let uu____16210 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____16210
                                              in
                                           solve env uu____16209))
                             | (x,imp)::formals2 ->
                                 let uu____16232 =
                                   let uu____16239 =
                                     let uu____16242 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____16242
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____16239 wl1
                                    in
                                 (match uu____16232 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____16263 =
                                          let uu____16266 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____16266
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____16263 u_x
                                         in
                                      let uu____16267 =
                                        let uu____16270 =
                                          let uu____16273 =
                                            let uu____16274 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____16274, imp)  in
                                          [uu____16273]  in
                                        FStar_List.append bs_terms
                                          uu____16270
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____16267 formals2 wl2)
                              in
                           let uu____16301 = occurs_check u_lhs arrow1  in
                           (match uu____16301 with
                            | (uu____16314,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____16330 =
                                    let uu____16332 = FStar_Option.get msg
                                       in
                                    Prims.op_Hat "occurs-check failed: "
                                      uu____16332
                                     in
                                  giveup_or_defer env orig wl uu____16330
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
              (let uu____16365 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____16365
               then
                 let uu____16370 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____16373 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____16370 (rel_to_string (p_rel orig)) uu____16373
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____16500 = rhs wl1 scope env1 subst1  in
                     (match uu____16500 with
                      | (rhs_prob,wl2) ->
                          ((let uu____16521 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____16521
                            then
                              let uu____16526 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____16526
                            else ());
                           (let formula = p_guard rhs_prob  in
                            ((FStar_Util.Inl ([rhs_prob], formula)), wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____16604 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____16604 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2265_16606 = hd1  in
                       let uu____16607 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2265_16606.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2265_16606.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____16607
                       }  in
                     let hd21 =
                       let uu___2268_16611 = hd2  in
                       let uu____16612 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2268_16611.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2268_16611.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____16612
                       }  in
                     let uu____16615 =
                       let uu____16620 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____16620
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____16615 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____16641 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____16641
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____16648 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____16648 with
                           | (FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____16715 =
                                   FStar_TypeChecker_Env.close_forall env2
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____16715
                                  in
                               ((let uu____16733 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env2)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16733
                                 then
                                   let uu____16738 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____16740 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____16738
                                     uu____16740
                                 else ());
                                ((FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____16773 ->
                     ((FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16809 = aux wl [] env [] bs1 bs2  in
               match uu____16809 with
               | (FStar_Util.Inr msg,wl1) -> giveup env msg orig
               | (FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16864 = attempt sub_probs wl2  in
                   solve env uu____16864)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist ->
             (FStar_TypeChecker_Common.prob * Prims.string) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2303_16885 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              ctr = (uu___2303_16885.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2303_16885.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16898 = try_solve env wl'  in
          match uu____16898 with
          | Success (uu____16899,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 =
                  let uu___2312_16903 = wl  in
                  {
                    attempting = (uu___2312_16903.attempting);
                    wl_deferred = (uu___2312_16903.wl_deferred);
                    ctr = (uu___2312_16903.ctr);
                    defer_ok = (uu___2312_16903.defer_ok);
                    smt_ok = (uu___2312_16903.smt_ok);
                    umax_heuristic_ok = (uu___2312_16903.umax_heuristic_ok);
                    tcenv = (uu___2312_16903.tcenv);
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
        (let uu____16915 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16915 wl)

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
              let uu____16929 = FStar_List.map FStar_Pervasives_Native.fst bs
                 in
              FStar_Util.as_set uu____16929 FStar_Syntax_Syntax.order_bv  in
            let mk_solution env1 lhs1 bs rhs1 =
              let uu____16963 = lhs1  in
              match uu____16963 with
              | (uu____16966,ctx_u,uu____16968) ->
                  let sol =
                    match bs with
                    | [] -> rhs1
                    | uu____16976 ->
                        let uu____16977 = sn_binders env1 bs  in
                        u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                          uu____16977 rhs1
                     in
                  [TERM (ctx_u, sol)]
               in
            let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
              let uu____17026 = quasi_pattern env1 lhs1  in
              match uu____17026 with
              | FStar_Pervasives_Native.None  ->
                  ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
              | FStar_Pervasives_Native.Some (bs,uu____17060) ->
                  let uu____17065 = lhs1  in
                  (match uu____17065 with
                   | (t_lhs,ctx_u,args) ->
                       let uu____17080 = occurs_check ctx_u rhs1  in
                       (match uu____17080 with
                        | (uvars1,occurs_ok,msg) ->
                            if Prims.op_Negation occurs_ok
                            then
                              let uu____17131 =
                                let uu____17139 =
                                  let uu____17141 = FStar_Option.get msg  in
                                  Prims.op_Hat
                                    "quasi-pattern, occurs-check failed: "
                                    uu____17141
                                   in
                                FStar_Util.Inl uu____17139  in
                              (uu____17131, wl1)
                            else
                              (let fvs_lhs =
                                 binders_as_bv_set
                                   (FStar_List.append
                                      ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                      bs)
                                  in
                               let fvs_rhs = FStar_Syntax_Free.names rhs1  in
                               let uu____17169 =
                                 let uu____17171 =
                                   FStar_Util.set_is_subset_of fvs_rhs
                                     fvs_lhs
                                    in
                                 Prims.op_Negation uu____17171  in
                               if uu____17169
                               then
                                 ((FStar_Util.Inl
                                     "quasi-pattern, free names on the RHS are not included in the LHS"),
                                   wl1)
                               else
                                 (let uu____17198 =
                                    let uu____17206 =
                                      mk_solution env1 lhs1 bs rhs1  in
                                    FStar_Util.Inr uu____17206  in
                                  let uu____17212 =
                                    restrict_all_uvars ctx_u uvars1 wl1  in
                                  (uu____17198, uu____17212)))))
               in
            let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
              let uu____17256 = FStar_Syntax_Util.head_and_args rhs1  in
              match uu____17256 with
              | (rhs_hd,args) ->
                  let uu____17299 = FStar_Util.prefix args  in
                  (match uu____17299 with
                   | (args_rhs,last_arg_rhs) ->
                       let rhs' =
                         FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                           FStar_Pervasives_Native.None
                           rhs1.FStar_Syntax_Syntax.pos
                          in
                       let uu____17371 = lhs1  in
                       (match uu____17371 with
                        | (t_lhs,u_lhs,_lhs_args) ->
                            let uu____17375 =
                              let uu____17386 =
                                let uu____17393 =
                                  let uu____17396 =
                                    FStar_Syntax_Util.type_u ()  in
                                  FStar_All.pipe_left
                                    FStar_Pervasives_Native.fst uu____17396
                                   in
                                copy_uvar u_lhs [] uu____17393 wl1  in
                              match uu____17386 with
                              | (uu____17423,t_last_arg,wl2) ->
                                  let uu____17426 =
                                    let uu____17433 =
                                      let uu____17434 =
                                        let uu____17443 =
                                          FStar_Syntax_Syntax.null_binder
                                            t_last_arg
                                           in
                                        [uu____17443]  in
                                      FStar_List.append bs_lhs uu____17434
                                       in
                                    copy_uvar u_lhs uu____17433 t_res_lhs wl2
                                     in
                                  (match uu____17426 with
                                   | (uu____17478,lhs',wl3) ->
                                       let uu____17481 =
                                         copy_uvar u_lhs bs_lhs t_last_arg
                                           wl3
                                          in
                                       (match uu____17481 with
                                        | (uu____17498,lhs'_last_arg,wl4) ->
                                            (lhs', lhs'_last_arg, wl4)))
                               in
                            (match uu____17375 with
                             | (lhs',lhs'_last_arg,wl2) ->
                                 let sol =
                                   let uu____17519 =
                                     let uu____17520 =
                                       let uu____17525 =
                                         let uu____17526 =
                                           let uu____17529 =
                                             let uu____17534 =
                                               let uu____17535 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   lhs'_last_arg
                                                  in
                                               [uu____17535]  in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               lhs' uu____17534
                                              in
                                           uu____17529
                                             FStar_Pervasives_Native.None
                                             t_lhs.FStar_Syntax_Syntax.pos
                                            in
                                         FStar_Syntax_Util.abs bs_lhs
                                           uu____17526
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Syntax_Util.residual_tot
                                                 t_res_lhs))
                                          in
                                       (u_lhs, uu____17525)  in
                                     TERM uu____17520  in
                                   [uu____17519]  in
                                 let uu____17560 =
                                   let uu____17567 =
                                     mk_t_problem wl2 [] orig1 lhs'
                                       FStar_TypeChecker_Common.EQ rhs'
                                       FStar_Pervasives_Native.None
                                       "first-order lhs"
                                      in
                                   match uu____17567 with
                                   | (p1,wl3) ->
                                       let uu____17587 =
                                         mk_t_problem wl3 [] orig1
                                           lhs'_last_arg
                                           FStar_TypeChecker_Common.EQ
                                           (FStar_Pervasives_Native.fst
                                              last_arg_rhs)
                                           FStar_Pervasives_Native.None
                                           "first-order rhs"
                                          in
                                       (match uu____17587 with
                                        | (p2,wl4) -> ([p1; p2], wl4))
                                    in
                                 (match uu____17560 with
                                  | (sub_probs,wl3) ->
                                      let uu____17619 =
                                        let uu____17620 =
                                          solve_prob orig1
                                            FStar_Pervasives_Native.None sol
                                            wl3
                                           in
                                        attempt sub_probs uu____17620  in
                                      solve env1 uu____17619))))
               in
            let first_order orig1 env1 wl1 lhs1 rhs1 =
              let is_app rhs2 =
                let uu____17654 = FStar_Syntax_Util.head_and_args rhs2  in
                match uu____17654 with
                | (uu____17672,args) ->
                    (match args with | [] -> false | uu____17708 -> true)
                 in
              let is_arrow rhs2 =
                let uu____17727 =
                  let uu____17728 = FStar_Syntax_Subst.compress rhs2  in
                  uu____17728.FStar_Syntax_Syntax.n  in
                match uu____17727 with
                | FStar_Syntax_Syntax.Tm_arrow uu____17732 -> true
                | uu____17748 -> false  in
              let uu____17750 = quasi_pattern env1 lhs1  in
              match uu____17750 with
              | FStar_Pervasives_Native.None  ->
                  let uu____17761 =
                    let uu____17763 = prob_to_string env1 orig1  in
                    FStar_Util.format1
                      "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                      uu____17763
                     in
                  giveup_or_defer env1 orig1 wl1 uu____17761
              | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                  let uu____17772 = is_app rhs1  in
                  if uu____17772
                  then imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                  else
                    (let uu____17777 = is_arrow rhs1  in
                     if uu____17777
                     then
                       imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                         FStar_TypeChecker_Common.EQ rhs1
                     else
                       (let uu____17782 =
                          let uu____17784 = prob_to_string env1 orig1  in
                          FStar_Util.format1
                            "first_order heuristic cannot solve %s; rhs not an app or arrow"
                            uu____17784
                           in
                        giveup_or_defer env1 orig1 wl1 uu____17782))
               in
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-rigid subtyping"
                else solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17795 = lhs  in
                (match uu____17795 with
                 | (_t1,ctx_uv,args_lhs) ->
                     let uu____17799 =
                       pat_vars env
                         ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders args_lhs
                        in
                     (match uu____17799 with
                      | FStar_Pervasives_Native.Some lhs_binders ->
                          let rhs1 = sn env rhs  in
                          let names_to_string1 fvs =
                            let uu____17817 =
                              let uu____17821 = FStar_Util.set_elements fvs
                                 in
                              FStar_List.map FStar_Syntax_Print.bv_to_string
                                uu____17821
                               in
                            FStar_All.pipe_right uu____17817
                              (FStar_String.concat ", ")
                             in
                          let fvs1 =
                            binders_as_bv_set
                              (FStar_List.append
                                 ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                 lhs_binders)
                             in
                          let fvs2 = FStar_Syntax_Free.names rhs1  in
                          let uu____17842 = occurs_check ctx_uv rhs1  in
                          (match uu____17842 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____17871 =
                                   let uu____17873 = FStar_Option.get msg  in
                                   Prims.op_Hat "occurs-check failed: "
                                     uu____17873
                                    in
                                 giveup_or_defer env orig wl uu____17871
                               else
                                 (let uu____17879 =
                                    FStar_Util.set_is_subset_of fvs2 fvs1  in
                                  if uu____17879
                                  then
                                    let sol =
                                      mk_solution env lhs lhs_binders rhs1
                                       in
                                    let wl1 =
                                      restrict_all_uvars ctx_uv uvars1 wl  in
                                    let uu____17886 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17886
                                  else
                                    if wl.defer_ok
                                    then
                                      (let uu____17890 =
                                         let uu____17892 =
                                           names_to_string1 fvs2  in
                                         let uu____17894 =
                                           names_to_string1 fvs1  in
                                         let uu____17896 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", "
                                             (FStar_List.append
                                                ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                lhs_binders)
                                            in
                                         FStar_Util.format3
                                           "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                           uu____17892 uu____17894
                                           uu____17896
                                          in
                                       giveup_or_defer env orig wl
                                         uu____17890)
                                    else first_order orig env wl lhs rhs1))
                      | uu____17908 ->
                          if wl.defer_ok
                          then giveup_or_defer env orig wl "Not a pattern"
                          else
                            (let uu____17915 =
                               try_quasi_pattern orig env wl lhs rhs  in
                             match uu____17915 with
                             | (FStar_Util.Inr sol,wl1) ->
                                 let uu____17941 =
                                   solve_prob orig
                                     FStar_Pervasives_Native.None sol wl1
                                    in
                                 solve env uu____17941
                             | (FStar_Util.Inl msg,uu____17943) ->
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
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then giveup_or_defer env orig wl "flex-flex subtyping"
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                if
                  wl.defer_ok &&
                    ((Prims.op_Negation (is_flex_pat lhs)) ||
                       (Prims.op_Negation (is_flex_pat rhs)))
                then giveup_or_defer env orig wl "flex-flex non-pattern"
                else
                  (let uu____17988 =
                     let uu____18005 = quasi_pattern env lhs  in
                     let uu____18012 = quasi_pattern env rhs  in
                     (uu____18005, uu____18012)  in
                   match uu____17988 with
                   | (FStar_Pervasives_Native.Some
                      (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                      (binders_rhs,t_res_rhs)) ->
                       let uu____18055 = lhs  in
                       (match uu____18055 with
                        | ({ FStar_Syntax_Syntax.n = uu____18056;
                             FStar_Syntax_Syntax.pos = range;
                             FStar_Syntax_Syntax.vars = uu____18058;_},u_lhs,uu____18060)
                            ->
                            let uu____18063 = rhs  in
                            (match uu____18063 with
                             | (uu____18064,u_rhs,uu____18066) ->
                                 let uu____18067 =
                                   (FStar_Syntax_Unionfind.equiv
                                      u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                      u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                     && (binders_eq binders_lhs binders_rhs)
                                    in
                                 if uu____18067
                                 then
                                   let uu____18074 =
                                     solve_prob orig
                                       FStar_Pervasives_Native.None [] wl
                                      in
                                   solve env uu____18074
                                 else
                                   (let uu____18077 =
                                      maximal_prefix
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                       in
                                    match uu____18077 with
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
                                        let uu____18109 =
                                          let uu____18116 =
                                            let uu____18119 =
                                              FStar_Syntax_Syntax.mk_Total
                                                t_res_lhs
                                               in
                                            FStar_Syntax_Util.arrow zs
                                              uu____18119
                                             in
                                          new_uvar
                                            (Prims.op_Hat "flex-flex quasi:"
                                               (Prims.op_Hat "\tlhs="
                                                  (Prims.op_Hat
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                     (Prims.op_Hat "\trhs="
                                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                            wl range gamma_w ctx_w
                                            uu____18116
                                            FStar_Syntax_Syntax.Strict
                                            FStar_Pervasives_Native.None
                                           in
                                        (match uu____18109 with
                                         | (uu____18131,w,wl1) ->
                                             let w_app =
                                               let uu____18137 =
                                                 let uu____18142 =
                                                   FStar_List.map
                                                     (fun uu____18153  ->
                                                        match uu____18153
                                                        with
                                                        | (z,uu____18161) ->
                                                            let uu____18166 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____18166) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____18142
                                                  in
                                               uu____18137
                                                 FStar_Pervasives_Native.None
                                                 w.FStar_Syntax_Syntax.pos
                                                in
                                             ((let uu____18168 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env)
                                                   (FStar_Options.Other "Rel")
                                                  in
                                               if uu____18168
                                               then
                                                 let uu____18173 =
                                                   let uu____18177 =
                                                     flex_t_to_string lhs  in
                                                   let uu____18179 =
                                                     let uu____18183 =
                                                       flex_t_to_string rhs
                                                        in
                                                     let uu____18185 =
                                                       let uu____18189 =
                                                         term_to_string w  in
                                                       let uu____18191 =
                                                         let uu____18195 =
                                                           FStar_Syntax_Print.binders_to_string
                                                             ", "
                                                             (FStar_List.append
                                                                ctx_l
                                                                binders_lhs)
                                                            in
                                                         let uu____18204 =
                                                           let uu____18208 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_r
                                                                  binders_rhs)
                                                              in
                                                           let uu____18217 =
                                                             let uu____18221
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", " zs
                                                                in
                                                             [uu____18221]
                                                              in
                                                           uu____18208 ::
                                                             uu____18217
                                                            in
                                                         uu____18195 ::
                                                           uu____18204
                                                          in
                                                       uu____18189 ::
                                                         uu____18191
                                                        in
                                                     uu____18183 ::
                                                       uu____18185
                                                      in
                                                   uu____18177 :: uu____18179
                                                    in
                                                 FStar_Util.print
                                                   "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                   uu____18173
                                               else ());
                                              (let sol =
                                                 let s1 =
                                                   let uu____18238 =
                                                     let uu____18243 =
                                                       FStar_Syntax_Util.abs
                                                         binders_lhs w_app
                                                         (FStar_Pervasives_Native.Some
                                                            (FStar_Syntax_Util.residual_tot
                                                               t_res_lhs))
                                                        in
                                                     (u_lhs, uu____18243)  in
                                                   TERM uu____18238  in
                                                 let uu____18244 =
                                                   FStar_Syntax_Unionfind.equiv
                                                     u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                     u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 if uu____18244
                                                 then [s1]
                                                 else
                                                   (let s2 =
                                                      let uu____18252 =
                                                        let uu____18257 =
                                                          FStar_Syntax_Util.abs
                                                            binders_rhs w_app
                                                            (FStar_Pervasives_Native.Some
                                                               (FStar_Syntax_Util.residual_tot
                                                                  t_res_lhs))
                                                           in
                                                        (u_rhs, uu____18257)
                                                         in
                                                      TERM uu____18252  in
                                                    [s1; s2])
                                                  in
                                               let uu____18258 =
                                                 solve_prob orig
                                                   FStar_Pervasives_Native.None
                                                   sol wl1
                                                  in
                                               solve env uu____18258))))))
                   | uu____18259 ->
                       giveup_or_defer env orig wl "flex-flex: non-patterns")

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____18330 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____18330
            then
              let uu____18335 = FStar_Syntax_Print.term_to_string t1  in
              let uu____18337 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____18339 = FStar_Syntax_Print.term_to_string t2  in
              let uu____18341 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____18335 uu____18337 uu____18339 uu____18341
            else ());
           (let uu____18352 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18352 with
            | (head1,args1) ->
                let uu____18395 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____18395 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____18465 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____18465 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              k false (defer "universe constraints" orig wl3))
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____18491 =
                         let uu____18493 =
                           FStar_Syntax_Print.term_to_string head1  in
                         let uu____18495 = args_to_string args1  in
                         let uu____18499 =
                           FStar_Syntax_Print.term_to_string head2  in
                         let uu____18501 = args_to_string args2  in
                         FStar_Util.format4
                           "unequal number of arguments: %s[%s] and %s[%s]"
                           uu____18493 uu____18495 uu____18499 uu____18501
                          in
                       giveup env1 uu____18491 orig
                     else
                       (let uu____18508 =
                          (nargs = Prims.int_zero) ||
                            (let uu____18513 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____18513 = FStar_Syntax_Util.Equal)
                           in
                        if uu____18508
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2561_18517 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2561_18517.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2561_18517.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2561_18517.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2561_18517.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2561_18517.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2561_18517.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2561_18517.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2561_18517.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____18527 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____18527
                                    else solve env1 wl2))
                        else
                          (let uu____18532 = base_and_refinement env1 t1  in
                           match uu____18532 with
                           | (base1,refinement1) ->
                               let uu____18557 = base_and_refinement env1 t2
                                  in
                               (match uu____18557 with
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
                                           let uu____18722 =
                                             FStar_List.fold_right
                                               (fun uu____18762  ->
                                                  fun uu____18763  ->
                                                    match (uu____18762,
                                                            uu____18763)
                                                    with
                                                    | (((a1,uu____18815),
                                                        (a2,uu____18817)),
                                                       (probs,wl3)) ->
                                                        let uu____18866 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18866
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____18722 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18909 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18909
                                                 then
                                                   let uu____18914 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18914
                                                 else ());
                                                (let uu____18920 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18920
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
                                                    (let uu____18947 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18947 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18963 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18963
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18971 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18971))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18995 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18995 with
                                                  | (subprobs,wl4) ->
                                                      let wl5 =
                                                        solve_prob orig
                                                          FStar_Pervasives_Native.None
                                                          [] wl4
                                                         in
                                                      let uu____19009 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____19009)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____19035 =
                                           match uu____19035 with
                                           | (prob,reason) ->
                                               ((let uu____19046 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____19046
                                                 then
                                                   let uu____19051 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____19053 =
                                                     prob_to_string env2 prob
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____19051 uu____19053
                                                     reason
                                                 else ());
                                                (let uu____19058 =
                                                   let uu____19067 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____19070 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____19067, uu____19070)
                                                    in
                                                 match uu____19058 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____19083 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____19083 with
                                                      | (head1',uu____19101)
                                                          ->
                                                          let uu____19126 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____19126
                                                           with
                                                           | (head2',uu____19144)
                                                               ->
                                                               let uu____19169
                                                                 =
                                                                 let uu____19174
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____19175
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____19174,
                                                                   uu____19175)
                                                                  in
                                                               (match uu____19169
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____19177
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____19177
                                                                    then
                                                                    let uu____19182
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____19184
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____19186
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____19188
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____19182
                                                                    uu____19184
                                                                    uu____19186
                                                                    uu____19188
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____19193
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2647_19201
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2647_19201.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____19203
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____19203
                                                                    then
                                                                    let uu____19208
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____19208
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____19213 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____19225 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____19225 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____19233 =
                                             let uu____19234 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____19234.FStar_Syntax_Syntax.n
                                              in
                                           match uu____19233 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____19239 -> false  in
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
                                          | uu____19242 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____19245 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2667_19281 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2667_19281.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2667_19281.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2667_19281.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2667_19281.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2667_19281.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2667_19281.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2667_19281.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2667_19281.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____19357 = destruct_flex_t scrutinee wl1  in
             match uu____19357 with
             | ((_t,uv,_args),wl2) ->
                 let uu____19368 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____19368 with
                  | (xs,pat_term,uu____19384,uu____19385) ->
                      let uu____19390 =
                        FStar_List.fold_left
                          (fun uu____19413  ->
                             fun x  ->
                               match uu____19413 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____19434 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____19434 with
                                    | (uu____19453,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____19390 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____19474 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____19474 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2707_19491 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    ctr = (uu___2707_19491.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2707_19491.umax_heuristic_ok);
                                    tcenv = (uu___2707_19491.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____19503 = solve env1 wl'  in
                                (match uu____19503 with
                                 | Success (uu____19506,imps) ->
                                     let wl'1 =
                                       let uu___2715_19509 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2715_19509.wl_deferred);
                                         ctr = (uu___2715_19509.ctr);
                                         defer_ok =
                                           (uu___2715_19509.defer_ok);
                                         smt_ok = (uu___2715_19509.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2715_19509.umax_heuristic_ok);
                                         tcenv = (uu___2715_19509.tcenv);
                                         wl_implicits =
                                           (uu___2715_19509.wl_implicits)
                                       }  in
                                     let uu____19510 = solve env1 wl'1  in
                                     (match uu____19510 with
                                      | Success (uu____19513,imps') ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           FStar_Pervasives_Native.Some
                                             ((let uu___2723_19517 = wl4  in
                                               {
                                                 attempting =
                                                   (uu___2723_19517.attempting);
                                                 wl_deferred =
                                                   (uu___2723_19517.wl_deferred);
                                                 ctr = (uu___2723_19517.ctr);
                                                 defer_ok =
                                                   (uu___2723_19517.defer_ok);
                                                 smt_ok =
                                                   (uu___2723_19517.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___2723_19517.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___2723_19517.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      wl4.wl_implicits
                                                      (FStar_List.append imps
                                                         imps'))
                                               })))
                                      | Failed uu____19518 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____19525 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____19548 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____19548
                 then
                   let uu____19553 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____19555 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____19553 uu____19555
                 else ());
                (let uu____19560 =
                   let uu____19581 =
                     let uu____19590 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____19590)  in
                   let uu____19597 =
                     let uu____19606 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____19606)  in
                   (uu____19581, uu____19597)  in
                 match uu____19560 with
                 | ((uu____19636,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____19639;
                                   FStar_Syntax_Syntax.vars = uu____19640;_}),
                    (s,t)) ->
                     let uu____19711 =
                       let uu____19713 = is_flex scrutinee  in
                       Prims.op_Negation uu____19713  in
                     if uu____19711
                     then
                       ((let uu____19724 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19724
                         then
                           let uu____19729 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19729
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19748 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19748
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19763 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19763
                           then
                             let uu____19768 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19770 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19768 uu____19770
                           else ());
                          (let pat_discriminates uu___28_19795 =
                             match uu___28_19795 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19811;
                                  FStar_Syntax_Syntax.p = uu____19812;_},FStar_Pervasives_Native.None
                                ,uu____19813) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19827;
                                  FStar_Syntax_Syntax.p = uu____19828;_},FStar_Pervasives_Native.None
                                ,uu____19829) -> true
                             | uu____19856 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19959 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19959 with
                                       | (uu____19961,uu____19962,t') ->
                                           let uu____19980 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19980 with
                                            | (FullMatch ,uu____19992) ->
                                                true
                                            | (HeadMatch
                                               uu____20006,uu____20007) ->
                                                true
                                            | uu____20022 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20059 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20059
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20070 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20070 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20158,uu____20159) ->
                                       branches1
                                   | uu____20304 -> branches  in
                                 let uu____20359 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20368 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20368 with
                                        | (p,uu____20372,uu____20373) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20402  -> FStar_Util.Inr _20402)
                                   uu____20359))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20432 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20432 with
                                | (p,uu____20441,e) ->
                                    ((let uu____20460 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20460
                                      then
                                        let uu____20465 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20467 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20465 uu____20467
                                      else ());
                                     (let uu____20472 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20487  -> FStar_Util.Inr _20487)
                                        uu____20472)))))
                 | ((s,t),(uu____20490,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____20493;
                                         FStar_Syntax_Syntax.vars =
                                           uu____20494;_}))
                     ->
                     let uu____20563 =
                       let uu____20565 = is_flex scrutinee  in
                       Prims.op_Negation uu____20565  in
                     if uu____20563
                     then
                       ((let uu____20576 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____20576
                         then
                           let uu____20581 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____20581
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____20600 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____20600
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____20615 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____20615
                           then
                             let uu____20620 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____20622 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____20620 uu____20622
                           else ());
                          (let pat_discriminates uu___28_20647 =
                             match uu___28_20647 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____20663;
                                  FStar_Syntax_Syntax.p = uu____20664;_},FStar_Pervasives_Native.None
                                ,uu____20665) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20679;
                                  FStar_Syntax_Syntax.p = uu____20680;_},FStar_Pervasives_Native.None
                                ,uu____20681) -> true
                             | uu____20708 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20811 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20811 with
                                       | (uu____20813,uu____20814,t') ->
                                           let uu____20832 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20832 with
                                            | (FullMatch ,uu____20844) ->
                                                true
                                            | (HeadMatch
                                               uu____20858,uu____20859) ->
                                                true
                                            | uu____20874 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20911 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20911
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20922 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20922 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____21010,uu____21011) ->
                                       branches1
                                   | uu____21156 -> branches  in
                                 let uu____21211 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____21220 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____21220 with
                                        | (p,uu____21224,uu____21225) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _21254  -> FStar_Util.Inr _21254)
                                   uu____21211))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____21284 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____21284 with
                                | (p,uu____21293,e) ->
                                    ((let uu____21312 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____21312
                                      then
                                        let uu____21317 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____21319 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____21317 uu____21319
                                      else ());
                                     (let uu____21324 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _21339  -> FStar_Util.Inr _21339)
                                        uu____21324)))))
                 | uu____21340 ->
                     ((let uu____21362 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____21362
                       then
                         let uu____21367 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____21369 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____21367 uu____21369
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____21415 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____21415
            then
              let uu____21420 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____21422 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____21424 = FStar_Syntax_Print.term_to_string t1  in
              let uu____21426 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____21420 uu____21422 uu____21424 uu____21426
            else ());
           (let uu____21431 = head_matches_delta env1 wl1 t1 t2  in
            match uu____21431 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____21462,uu____21463) ->
                     let rec may_relate head3 =
                       let uu____21491 =
                         let uu____21492 = FStar_Syntax_Subst.compress head3
                            in
                         uu____21492.FStar_Syntax_Syntax.n  in
                       match uu____21491 with
                       | FStar_Syntax_Syntax.Tm_name uu____21496 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____21498 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____21523 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____21523 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____21525 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____21528
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____21529 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____21532,uu____21533) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____21575) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____21581) ->
                           may_relate t
                       | uu____21586 -> false  in
                     let uu____21588 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____21588 with
                      | FStar_Util.Inl _defer_ok ->
                          giveup_or_defer1 orig "delaying match heuristic"
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let in_inverses_case =
                            let uu____21654 = lookup_inverses t1  in
                            match uu____21654 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____21765 = lookup_inverses t2  in
                                (match uu____21765 with
                                 | FStar_Pervasives_Native.None  ->
                                     FStar_Pervasives_Native.None
                                 | FStar_Pervasives_Native.Some p ->
                                     FStar_Pervasives_Native.Some (p, t2, t1))
                            | FStar_Pervasives_Native.Some p ->
                                FStar_Pervasives_Native.Some (p, t1, t2)
                             in
                          let uu____22204 =
                            FStar_All.pipe_right in_inverses_case
                              FStar_Util.is_some
                             in
                          if uu____22204
                          then
                            let uu____22294 =
                              FStar_All.pipe_right in_inverses_case
                                FStar_Util.must
                               in
                            (match uu____22294 with
                             | ((univs1,args,t,t_uvar,inv_fv),t11,t21) ->
                                 let uu____22558 =
                                   let k =
                                     let uu____22568 =
                                       env1.FStar_TypeChecker_Env.tc_term
                                         (let uu___2893_22576 = env1  in
                                          {
                                            FStar_TypeChecker_Env.solver =
                                              (uu___2893_22576.FStar_TypeChecker_Env.solver);
                                            FStar_TypeChecker_Env.range =
                                              (uu___2893_22576.FStar_TypeChecker_Env.range);
                                            FStar_TypeChecker_Env.curmodule =
                                              (uu___2893_22576.FStar_TypeChecker_Env.curmodule);
                                            FStar_TypeChecker_Env.gamma =
                                              (uu___2893_22576.FStar_TypeChecker_Env.gamma);
                                            FStar_TypeChecker_Env.gamma_sig =
                                              (uu___2893_22576.FStar_TypeChecker_Env.gamma_sig);
                                            FStar_TypeChecker_Env.gamma_cache
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.gamma_cache);
                                            FStar_TypeChecker_Env.modules =
                                              (uu___2893_22576.FStar_TypeChecker_Env.modules);
                                            FStar_TypeChecker_Env.expected_typ
                                              = FStar_Pervasives_Native.None;
                                            FStar_TypeChecker_Env.sigtab =
                                              (uu___2893_22576.FStar_TypeChecker_Env.sigtab);
                                            FStar_TypeChecker_Env.attrtab =
                                              (uu___2893_22576.FStar_TypeChecker_Env.attrtab);
                                            FStar_TypeChecker_Env.instantiate_imp
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.instantiate_imp);
                                            FStar_TypeChecker_Env.effects =
                                              (uu___2893_22576.FStar_TypeChecker_Env.effects);
                                            FStar_TypeChecker_Env.generalize
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.generalize);
                                            FStar_TypeChecker_Env.letrecs =
                                              (uu___2893_22576.FStar_TypeChecker_Env.letrecs);
                                            FStar_TypeChecker_Env.top_level =
                                              (uu___2893_22576.FStar_TypeChecker_Env.top_level);
                                            FStar_TypeChecker_Env.check_uvars
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.check_uvars);
                                            FStar_TypeChecker_Env.use_eq =
                                              (uu___2893_22576.FStar_TypeChecker_Env.use_eq);
                                            FStar_TypeChecker_Env.is_iface =
                                              (uu___2893_22576.FStar_TypeChecker_Env.is_iface);
                                            FStar_TypeChecker_Env.admit =
                                              (uu___2893_22576.FStar_TypeChecker_Env.admit);
                                            FStar_TypeChecker_Env.lax = true;
                                            FStar_TypeChecker_Env.lax_universes
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.lax_universes);
                                            FStar_TypeChecker_Env.phase1 =
                                              (uu___2893_22576.FStar_TypeChecker_Env.phase1);
                                            FStar_TypeChecker_Env.failhard =
                                              (uu___2893_22576.FStar_TypeChecker_Env.failhard);
                                            FStar_TypeChecker_Env.nosynth =
                                              (uu___2893_22576.FStar_TypeChecker_Env.nosynth);
                                            FStar_TypeChecker_Env.uvar_subtyping
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.uvar_subtyping);
                                            FStar_TypeChecker_Env.tc_term =
                                              (uu___2893_22576.FStar_TypeChecker_Env.tc_term);
                                            FStar_TypeChecker_Env.type_of =
                                              (uu___2893_22576.FStar_TypeChecker_Env.type_of);
                                            FStar_TypeChecker_Env.universe_of
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.universe_of);
                                            FStar_TypeChecker_Env.check_type_of
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.check_type_of);
                                            FStar_TypeChecker_Env.use_bv_sorts
                                              = true;
                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.qtbl_name_and_index);
                                            FStar_TypeChecker_Env.normalized_eff_names
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.normalized_eff_names);
                                            FStar_TypeChecker_Env.fv_delta_depths
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.fv_delta_depths);
                                            FStar_TypeChecker_Env.proof_ns =
                                              (uu___2893_22576.FStar_TypeChecker_Env.proof_ns);
                                            FStar_TypeChecker_Env.synth_hook
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.synth_hook);
                                            FStar_TypeChecker_Env.splice =
                                              (uu___2893_22576.FStar_TypeChecker_Env.splice);
                                            FStar_TypeChecker_Env.mpreprocess
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.mpreprocess);
                                            FStar_TypeChecker_Env.postprocess
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.postprocess);
                                            FStar_TypeChecker_Env.is_native_tactic
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.is_native_tactic);
                                            FStar_TypeChecker_Env.identifier_info
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.identifier_info);
                                            FStar_TypeChecker_Env.tc_hooks =
                                              (uu___2893_22576.FStar_TypeChecker_Env.tc_hooks);
                                            FStar_TypeChecker_Env.dsenv =
                                              (uu___2893_22576.FStar_TypeChecker_Env.dsenv);
                                            FStar_TypeChecker_Env.nbe =
                                              (uu___2893_22576.FStar_TypeChecker_Env.nbe);
                                            FStar_TypeChecker_Env.strict_args_tab
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.strict_args_tab);
                                            FStar_TypeChecker_Env.erasable_types_tab
                                              =
                                              (uu___2893_22576.FStar_TypeChecker_Env.erasable_types_tab)
                                          }) t11
                                        in
                                     match uu____22568 with
                                     | (uu____22581,lc,uu____22583) ->
                                         lc.FStar_Syntax_Syntax.res_typ
                                      in
                                   let uu____22584 =
                                     FStar_All.pipe_right t_uvar
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar uu____22584 [] k wl1  in
                                 (match uu____22558 with
                                  | (uu____22611,new_uv_t,wl2) ->
                                      let uu____22614 =
                                        mk_t_problem wl2 [] orig new_uv_t
                                          FStar_TypeChecker_Common.EQ t21
                                          FStar_Pervasives_Native.None
                                          "sub-problem 1 of inverses case"
                                         in
                                      (match uu____22614 with
                                       | (sub_prob1,wl3) ->
                                           let inv_t2 =
                                             let fv_tm =
                                               FStar_All.pipe_right inv_fv
                                                 FStar_Syntax_Syntax.fv_to_tm
                                                in
                                             let head3 =
                                               if
                                                 (FStar_List.length univs1) =
                                                   Prims.int_zero
                                               then fv_tm
                                               else
                                                 FStar_Syntax_Syntax.mk_Tm_uinst
                                                   fv_tm univs1
                                                in
                                             let uu____22638 =
                                               let uu____22643 =
                                                 let uu____22644 =
                                                   let uu____22655 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t21
                                                      in
                                                   [uu____22655]  in
                                                 FStar_List.append args
                                                   uu____22644
                                                  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 head3 uu____22643
                                                in
                                             uu____22638
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           let uu____22688 =
                                             mk_t_problem wl3 [] orig t
                                               FStar_TypeChecker_Common.EQ
                                               inv_t2
                                               FStar_Pervasives_Native.None
                                               "sub-problem 2 of inverses case"
                                              in
                                           (match uu____22688 with
                                            | (sub_prob2,wl4) ->
                                                let wl5 =
                                                  let uu____22703 =
                                                    let uu____22706 =
                                                      FStar_Syntax_Util.mk_conj
                                                        (p_guard sub_prob1)
                                                        (p_guard sub_prob2)
                                                       in
                                                    FStar_All.pipe_left
                                                      (fun _22709  ->
                                                         FStar_Pervasives_Native.Some
                                                           _22709)
                                                      uu____22706
                                                     in
                                                  solve_prob orig uu____22703
                                                    [] wl4
                                                   in
                                                let uu____22710 =
                                                  attempt
                                                    [sub_prob1; sub_prob2]
                                                    wl5
                                                   in
                                                solve env1 uu____22710))))
                          else
                            (let uu____22713 =
                               ((may_relate head1) || (may_relate head2)) &&
                                 wl1.smt_ok
                                in
                             if uu____22713
                             then
                               let uu____22716 =
                                 guard_of_prob env1 wl1 problem t1 t2  in
                               match uu____22716 with
                               | (guard,wl2) ->
                                   let uu____22723 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some guard)
                                       [] wl2
                                      in
                                   solve env1 uu____22723
                             else
                               (let uu____22726 =
                                  let uu____22728 =
                                    FStar_Syntax_Print.term_to_string head1
                                     in
                                  let uu____22730 =
                                    let uu____22732 =
                                      let uu____22736 =
                                        delta_depth_of_term env1 head1  in
                                      FStar_Util.bind_opt uu____22736
                                        (fun x  ->
                                           let uu____22743 =
                                             FStar_Syntax_Print.delta_depth_to_string
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____22743)
                                       in
                                    FStar_Util.dflt "" uu____22732  in
                                  let uu____22748 =
                                    FStar_Syntax_Print.term_to_string head2
                                     in
                                  let uu____22750 =
                                    let uu____22752 =
                                      let uu____22756 =
                                        delta_depth_of_term env1 head2  in
                                      FStar_Util.bind_opt uu____22756
                                        (fun x  ->
                                           let uu____22763 =
                                             FStar_Syntax_Print.delta_depth_to_string
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____22763)
                                       in
                                    FStar_Util.dflt "" uu____22752  in
                                  FStar_Util.format4
                                    "head mismatch (%s (%s) vs %s (%s))"
                                    uu____22728 uu____22730 uu____22748
                                    uu____22750
                                   in
                                giveup env1 uu____22726 orig)))
                 | (HeadMatch (true ),uu____22769) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____22784 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____22784 with
                        | (guard,wl2) ->
                            let uu____22791 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____22791)
                     else
                       (let uu____22794 =
                          let uu____22796 =
                            FStar_Syntax_Print.term_to_string t1  in
                          let uu____22798 =
                            FStar_Syntax_Print.term_to_string t2  in
                          FStar_Util.format2
                            "head mismatch for subtyping (%s vs %s)"
                            uu____22796 uu____22798
                           in
                        giveup env1 uu____22794 orig)
                 | (uu____22801,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2935_22815 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2935_22815.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2935_22815.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2935_22815.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2935_22815.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2935_22815.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2935_22815.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2935_22815.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2935_22815.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____22842 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____22842
          then
            let uu____22845 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____22845
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____22851 =
                let uu____22854 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____22854  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____22851 t1);
             (let uu____22873 =
                let uu____22876 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____22876  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____22873 t2);
             (let uu____22895 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____22895
              then
                let uu____22899 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____22901 =
                  let uu____22903 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____22905 =
                    let uu____22907 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____22907  in
                  Prims.op_Hat uu____22903 uu____22905  in
                let uu____22910 =
                  let uu____22912 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____22914 =
                    let uu____22916 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____22916  in
                  Prims.op_Hat uu____22912 uu____22914  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____22899 uu____22901 uu____22910
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____22923,uu____22924) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____22948,FStar_Syntax_Syntax.Tm_delayed uu____22949) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____22973,uu____22974) ->
                  let uu____23001 =
                    let uu___2966_23002 = problem  in
                    let uu____23003 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2966_23002.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____23003;
                      FStar_TypeChecker_Common.relation =
                        (uu___2966_23002.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2966_23002.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2966_23002.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2966_23002.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2966_23002.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2966_23002.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2966_23002.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2966_23002.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____23001 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____23004,uu____23005) ->
                  let uu____23012 =
                    let uu___2972_23013 = problem  in
                    let uu____23014 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2972_23013.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____23014;
                      FStar_TypeChecker_Common.relation =
                        (uu___2972_23013.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2972_23013.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2972_23013.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2972_23013.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2972_23013.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2972_23013.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2972_23013.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2972_23013.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____23012 wl
              | (uu____23015,FStar_Syntax_Syntax.Tm_ascribed uu____23016) ->
                  let uu____23043 =
                    let uu___2978_23044 = problem  in
                    let uu____23045 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2978_23044.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2978_23044.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2978_23044.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____23045;
                      FStar_TypeChecker_Common.element =
                        (uu___2978_23044.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2978_23044.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2978_23044.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2978_23044.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2978_23044.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2978_23044.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____23043 wl
              | (uu____23046,FStar_Syntax_Syntax.Tm_meta uu____23047) ->
                  let uu____23054 =
                    let uu___2984_23055 = problem  in
                    let uu____23056 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2984_23055.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2984_23055.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2984_23055.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____23056;
                      FStar_TypeChecker_Common.element =
                        (uu___2984_23055.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2984_23055.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2984_23055.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2984_23055.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2984_23055.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2984_23055.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____23054 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____23058),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____23060)) ->
                  let uu____23069 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____23069
              | (FStar_Syntax_Syntax.Tm_bvar uu____23070,uu____23071) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____23073,FStar_Syntax_Syntax.Tm_bvar uu____23074) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_23144 =
                    match uu___29_23144 with
                    | [] -> c
                    | bs ->
                        let uu____23172 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____23172
                     in
                  let uu____23183 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____23183 with
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
                                    let uu____23332 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____23332
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
                  let mk_t t l uu___30_23421 =
                    match uu___30_23421 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____23463 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____23463 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____23608 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____23609 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____23608
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____23609 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____23611,uu____23612) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____23643 -> true
                    | uu____23663 -> false  in
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
                      (let uu____23723 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3086_23731 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3086_23731.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3086_23731.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3086_23731.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3086_23731.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3086_23731.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3086_23731.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3086_23731.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3086_23731.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3086_23731.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3086_23731.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3086_23731.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3086_23731.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3086_23731.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3086_23731.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3086_23731.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3086_23731.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3086_23731.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3086_23731.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3086_23731.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3086_23731.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3086_23731.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3086_23731.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3086_23731.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3086_23731.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3086_23731.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3086_23731.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3086_23731.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3086_23731.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3086_23731.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3086_23731.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3086_23731.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3086_23731.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3086_23731.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3086_23731.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3086_23731.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3086_23731.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3086_23731.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3086_23731.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3086_23731.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3086_23731.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3086_23731.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3086_23731.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____23723 with
                       | (uu____23736,ty,uu____23738) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____23747 =
                                 let uu____23748 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____23748.FStar_Syntax_Syntax.n  in
                               match uu____23747 with
                               | FStar_Syntax_Syntax.Tm_refine uu____23751 ->
                                   let uu____23758 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____23758
                               | uu____23759 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____23762 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____23762
                             then
                               let uu____23767 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____23769 =
                                 let uu____23771 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____23771
                                  in
                               let uu____23772 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____23767 uu____23769 uu____23772
                             else ());
                            r1))
                     in
                  let uu____23777 =
                    let uu____23794 = maybe_eta t1  in
                    let uu____23801 = maybe_eta t2  in
                    (uu____23794, uu____23801)  in
                  (match uu____23777 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3107_23843 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3107_23843.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3107_23843.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3107_23843.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3107_23843.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3107_23843.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3107_23843.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3107_23843.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3107_23843.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____23864 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____23864
                       then
                         let uu____23867 = destruct_flex_t not_abs wl  in
                         (match uu____23867 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3124_23884 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3124_23884.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3124_23884.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3124_23884.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3124_23884.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3124_23884.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3124_23884.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3124_23884.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3124_23884.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____23908 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____23908
                       then
                         let uu____23911 = destruct_flex_t not_abs wl  in
                         (match uu____23911 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3124_23928 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3124_23928.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3124_23928.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3124_23928.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3124_23928.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3124_23928.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3124_23928.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3124_23928.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3124_23928.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____23932 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____23950,FStar_Syntax_Syntax.Tm_abs uu____23951) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____23982 -> true
                    | uu____24002 -> false  in
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
                      (let uu____24062 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3086_24070 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3086_24070.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3086_24070.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3086_24070.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3086_24070.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3086_24070.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3086_24070.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3086_24070.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3086_24070.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3086_24070.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3086_24070.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3086_24070.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3086_24070.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3086_24070.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3086_24070.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3086_24070.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3086_24070.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3086_24070.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3086_24070.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3086_24070.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3086_24070.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3086_24070.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3086_24070.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3086_24070.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3086_24070.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3086_24070.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3086_24070.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3086_24070.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3086_24070.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3086_24070.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3086_24070.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3086_24070.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3086_24070.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3086_24070.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3086_24070.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3086_24070.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3086_24070.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3086_24070.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3086_24070.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3086_24070.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3086_24070.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3086_24070.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3086_24070.FStar_TypeChecker_Env.erasable_types_tab)
                            }) t
                          in
                       match uu____24062 with
                       | (uu____24075,ty,uu____24077) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____24086 =
                                 let uu____24087 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____24087.FStar_Syntax_Syntax.n  in
                               match uu____24086 with
                               | FStar_Syntax_Syntax.Tm_refine uu____24090 ->
                                   let uu____24097 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____24097
                               | uu____24098 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____24101 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____24101
                             then
                               let uu____24106 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____24108 =
                                 let uu____24110 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____24110
                                  in
                               let uu____24111 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____24106 uu____24108 uu____24111
                             else ());
                            r1))
                     in
                  let uu____24116 =
                    let uu____24133 = maybe_eta t1  in
                    let uu____24140 = maybe_eta t2  in
                    (uu____24133, uu____24140)  in
                  (match uu____24116 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3107_24182 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3107_24182.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3107_24182.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3107_24182.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3107_24182.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3107_24182.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3107_24182.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3107_24182.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3107_24182.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____24203 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____24203
                       then
                         let uu____24206 = destruct_flex_t not_abs wl  in
                         (match uu____24206 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3124_24223 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3124_24223.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3124_24223.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3124_24223.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3124_24223.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3124_24223.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3124_24223.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3124_24223.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3124_24223.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____24247 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____24247
                       then
                         let uu____24250 = destruct_flex_t not_abs wl  in
                         (match uu____24250 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3124_24267 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3124_24267.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3124_24267.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3124_24267.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3124_24267.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3124_24267.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3124_24267.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3124_24267.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3124_24267.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            giveup env
                              "head tag mismatch: RHS is an abstraction" orig)
                   | uu____24271 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____24301 =
                    let uu____24306 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____24306 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3147_24334 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3147_24334.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3147_24334.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3149_24336 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3149_24336.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3149_24336.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____24337,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3147_24352 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3147_24352.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3147_24352.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3149_24354 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3149_24354.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3149_24354.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____24355 -> (x1, x2)  in
                  (match uu____24301 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____24374 = as_refinement false env t11  in
                       (match uu____24374 with
                        | (x12,phi11) ->
                            let uu____24382 = as_refinement false env t21  in
                            (match uu____24382 with
                             | (x22,phi21) ->
                                 ((let uu____24391 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____24391
                                   then
                                     ((let uu____24396 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____24398 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____24400 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____24396
                                         uu____24398 uu____24400);
                                      (let uu____24403 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____24405 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____24407 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____24403
                                         uu____24405 uu____24407))
                                   else ());
                                  (let uu____24412 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____24412 with
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
                                         let uu____24483 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____24483
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____24495 =
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
                                         (let uu____24508 =
                                            let uu____24511 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____24511
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____24508
                                            (p_guard base_prob));
                                         (let uu____24530 =
                                            let uu____24533 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____24533
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____24530
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____24552 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____24552)
                                          in
                                       let has_uvars =
                                         (let uu____24557 =
                                            let uu____24559 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____24559
                                             in
                                          Prims.op_Negation uu____24557) ||
                                           (let uu____24563 =
                                              let uu____24565 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____24565
                                               in
                                            Prims.op_Negation uu____24563)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____24569 =
                                           let uu____24574 =
                                             let uu____24583 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____24583]  in
                                           mk_t_problem wl1 uu____24574 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____24569 with
                                          | (ref_prob,wl2) ->
                                              let uu____24605 =
                                                solve env1
                                                  (let uu___3191_24607 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     ctr =
                                                       (uu___3191_24607.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3191_24607.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3191_24607.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3191_24607.tcenv);
                                                     wl_implicits =
                                                       (uu___3191_24607.wl_implicits)
                                                   })
                                                 in
                                              (match uu____24605 with
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
                                               | Success uu____24624 ->
                                                   let guard =
                                                     let uu____24632 =
                                                       FStar_All.pipe_right
                                                         (p_guard ref_prob)
                                                         (guard_on_element
                                                            wl2 problem x13)
                                                        in
                                                     FStar_Syntax_Util.mk_conj
                                                       (p_guard base_prob)
                                                       uu____24632
                                                      in
                                                   let wl3 =
                                                     solve_prob orig
                                                       (FStar_Pervasives_Native.Some
                                                          guard) [] wl2
                                                      in
                                                   let wl4 =
                                                     let uu___3202_24641 =
                                                       wl3  in
                                                     {
                                                       attempting =
                                                         (uu___3202_24641.attempting);
                                                       wl_deferred =
                                                         (uu___3202_24641.wl_deferred);
                                                       ctr =
                                                         (wl3.ctr +
                                                            Prims.int_one);
                                                       defer_ok =
                                                         (uu___3202_24641.defer_ok);
                                                       smt_ok =
                                                         (uu___3202_24641.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___3202_24641.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___3202_24641.tcenv);
                                                       wl_implicits =
                                                         (uu___3202_24641.wl_implicits)
                                                     }  in
                                                   let uu____24643 =
                                                     attempt [base_prob] wl4
                                                      in
                                                   solve env1 uu____24643))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____24646,FStar_Syntax_Syntax.Tm_uvar uu____24647) ->
                  let uu____24672 = destruct_flex_t t1 wl  in
                  (match uu____24672 with
                   | (f1,wl1) ->
                       let uu____24679 = destruct_flex_t t2 wl1  in
                       (match uu____24679 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24686;
                    FStar_Syntax_Syntax.pos = uu____24687;
                    FStar_Syntax_Syntax.vars = uu____24688;_},uu____24689),FStar_Syntax_Syntax.Tm_uvar
                 uu____24690) ->
                  let uu____24739 = destruct_flex_t t1 wl  in
                  (match uu____24739 with
                   | (f1,wl1) ->
                       let uu____24746 = destruct_flex_t t2 wl1  in
                       (match uu____24746 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____24753,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24754;
                    FStar_Syntax_Syntax.pos = uu____24755;
                    FStar_Syntax_Syntax.vars = uu____24756;_},uu____24757))
                  ->
                  let uu____24806 = destruct_flex_t t1 wl  in
                  (match uu____24806 with
                   | (f1,wl1) ->
                       let uu____24813 = destruct_flex_t t2 wl1  in
                       (match uu____24813 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24820;
                    FStar_Syntax_Syntax.pos = uu____24821;
                    FStar_Syntax_Syntax.vars = uu____24822;_},uu____24823),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24824;
                    FStar_Syntax_Syntax.pos = uu____24825;
                    FStar_Syntax_Syntax.vars = uu____24826;_},uu____24827))
                  ->
                  let uu____24900 = destruct_flex_t t1 wl  in
                  (match uu____24900 with
                   | (f1,wl1) ->
                       let uu____24907 = destruct_flex_t t2 wl1  in
                       (match uu____24907 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____24914,uu____24915) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____24928 = destruct_flex_t t1 wl  in
                  (match uu____24928 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24935;
                    FStar_Syntax_Syntax.pos = uu____24936;
                    FStar_Syntax_Syntax.vars = uu____24937;_},uu____24938),uu____24939)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____24976 = destruct_flex_t t1 wl  in
                  (match uu____24976 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____24983,FStar_Syntax_Syntax.Tm_uvar uu____24984) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____24997,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____24998;
                    FStar_Syntax_Syntax.pos = uu____24999;
                    FStar_Syntax_Syntax.vars = uu____25000;_},uu____25001))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____25038,FStar_Syntax_Syntax.Tm_arrow uu____25039) ->
                  solve_t' env
                    (let uu___3302_25067 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3302_25067.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3302_25067.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3302_25067.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3302_25067.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3302_25067.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3302_25067.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3302_25067.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3302_25067.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3302_25067.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____25068;
                    FStar_Syntax_Syntax.pos = uu____25069;
                    FStar_Syntax_Syntax.vars = uu____25070;_},uu____25071),FStar_Syntax_Syntax.Tm_arrow
                 uu____25072) ->
                  solve_t' env
                    (let uu___3302_25124 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3302_25124.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3302_25124.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3302_25124.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3302_25124.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3302_25124.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3302_25124.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3302_25124.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3302_25124.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3302_25124.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____25125,FStar_Syntax_Syntax.Tm_uvar uu____25126) ->
                  let uu____25139 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____25139
              | (uu____25140,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____25141;
                    FStar_Syntax_Syntax.pos = uu____25142;
                    FStar_Syntax_Syntax.vars = uu____25143;_},uu____25144))
                  ->
                  let uu____25181 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____25181
              | (FStar_Syntax_Syntax.Tm_uvar uu____25182,uu____25183) ->
                  let uu____25196 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____25196
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____25197;
                    FStar_Syntax_Syntax.pos = uu____25198;
                    FStar_Syntax_Syntax.vars = uu____25199;_},uu____25200),uu____25201)
                  ->
                  let uu____25238 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____25238
              | (FStar_Syntax_Syntax.Tm_refine uu____25239,uu____25240) ->
                  let t21 =
                    let uu____25248 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____25248  in
                  solve_t env
                    (let uu___3337_25274 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3337_25274.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3337_25274.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3337_25274.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3337_25274.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3337_25274.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3337_25274.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3337_25274.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3337_25274.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3337_25274.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____25275,FStar_Syntax_Syntax.Tm_refine uu____25276) ->
                  let t11 =
                    let uu____25284 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____25284  in
                  solve_t env
                    (let uu___3344_25310 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3344_25310.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3344_25310.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3344_25310.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3344_25310.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3344_25310.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3344_25310.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3344_25310.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3344_25310.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3344_25310.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____25392 =
                    let uu____25393 = guard_of_prob env wl problem t1 t2  in
                    match uu____25393 with
                    | (guard,wl1) ->
                        let uu____25400 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____25400
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____25619 = br1  in
                        (match uu____25619 with
                         | (p1,w1,uu____25648) ->
                             let uu____25665 = br2  in
                             (match uu____25665 with
                              | (p2,w2,uu____25688) ->
                                  let uu____25693 =
                                    let uu____25695 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____25695  in
                                  if uu____25693
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____25722 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____25722 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____25759 = br2  in
                                         (match uu____25759 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____25792 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____25792
                                                 in
                                              let uu____25797 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____25828,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____25849) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____25908 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____25908 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____25797
                                                (fun uu____25980  ->
                                                   match uu____25980 with
                                                   | (wprobs,wl2) ->
                                                       let uu____26017 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____26017
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____26038
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____26038
                                                              then
                                                                let uu____26043
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____26045
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____26043
                                                                  uu____26045
                                                              else ());
                                                             (let uu____26051
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____26051
                                                                (fun
                                                                   uu____26087
                                                                    ->
                                                                   match uu____26087
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
                    | uu____26216 -> FStar_Pervasives_Native.None  in
                  let uu____26257 = solve_branches wl brs1 brs2  in
                  (match uu____26257 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else giveup env "Tm_match branches don't match" orig
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____26308 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____26308 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____26342 =
                                FStar_List.map
                                  (fun uu____26354  ->
                                     match uu____26354 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____26342  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____26363 =
                              let uu____26364 =
                                let uu____26365 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____26365
                                  (let uu___3443_26373 = wl3  in
                                   {
                                     attempting =
                                       (uu___3443_26373.attempting);
                                     wl_deferred =
                                       (uu___3443_26373.wl_deferred);
                                     ctr = (uu___3443_26373.ctr);
                                     defer_ok = (uu___3443_26373.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3443_26373.umax_heuristic_ok);
                                     tcenv = (uu___3443_26373.tcenv);
                                     wl_implicits =
                                       (uu___3443_26373.wl_implicits)
                                   })
                                 in
                              solve env uu____26364  in
                            (match uu____26363 with
                             | Success (ds,imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, imp))
                             | Failed uu____26378 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  by_smt ()))))
              | (FStar_Syntax_Syntax.Tm_match uu____26385,uu____26386) ->
                  let head1 =
                    let uu____26410 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26410
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26456 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26456
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26502 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26502
                    then
                      let uu____26506 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26508 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26510 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26506 uu____26508 uu____26510
                    else ());
                   (let no_free_uvars t =
                      (let uu____26524 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26524) &&
                        (let uu____26528 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26528)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26545 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26545 = FStar_Syntax_Util.Equal  in
                    let uu____26546 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26546
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26550 = equal t1 t2  in
                         (if uu____26550
                          then
                            let uu____26553 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26553
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26558 =
                            let uu____26565 = equal t1 t2  in
                            if uu____26565
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26578 = mk_eq2 wl env orig t1 t2  in
                               match uu____26578 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26558 with
                          | (guard,wl1) ->
                              let uu____26599 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26599))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____26602,uu____26603) ->
                  let head1 =
                    let uu____26611 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26611
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26657 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26657
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26703 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26703
                    then
                      let uu____26707 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26709 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26711 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26707 uu____26709 uu____26711
                    else ());
                   (let no_free_uvars t =
                      (let uu____26725 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26725) &&
                        (let uu____26729 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26729)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26746 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26746 = FStar_Syntax_Util.Equal  in
                    let uu____26747 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26747
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26751 = equal t1 t2  in
                         (if uu____26751
                          then
                            let uu____26754 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26754
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26759 =
                            let uu____26766 = equal t1 t2  in
                            if uu____26766
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26779 = mk_eq2 wl env orig t1 t2  in
                               match uu____26779 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26759 with
                          | (guard,wl1) ->
                              let uu____26800 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26800))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____26803,uu____26804) ->
                  let head1 =
                    let uu____26806 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26806
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26852 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26852
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26898 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26898
                    then
                      let uu____26902 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26904 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26906 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26902 uu____26904 uu____26906
                    else ());
                   (let no_free_uvars t =
                      (let uu____26920 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26920) &&
                        (let uu____26924 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26924)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26941 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26941 = FStar_Syntax_Util.Equal  in
                    let uu____26942 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26942
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26946 = equal t1 t2  in
                         (if uu____26946
                          then
                            let uu____26949 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26949
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26954 =
                            let uu____26961 = equal t1 t2  in
                            if uu____26961
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26974 = mk_eq2 wl env orig t1 t2  in
                               match uu____26974 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26954 with
                          | (guard,wl1) ->
                              let uu____26995 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26995))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____26998,uu____26999) ->
                  let head1 =
                    let uu____27001 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____27001
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____27047 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____27047
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____27093 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____27093
                    then
                      let uu____27097 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____27099 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____27101 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____27097 uu____27099 uu____27101
                    else ());
                   (let no_free_uvars t =
                      (let uu____27115 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____27115) &&
                        (let uu____27119 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____27119)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____27136 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____27136 = FStar_Syntax_Util.Equal  in
                    let uu____27137 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____27137
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____27141 = equal t1 t2  in
                         (if uu____27141
                          then
                            let uu____27144 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____27144
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____27149 =
                            let uu____27156 = equal t1 t2  in
                            if uu____27156
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27169 = mk_eq2 wl env orig t1 t2  in
                               match uu____27169 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____27149 with
                          | (guard,wl1) ->
                              let uu____27190 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____27190))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____27193,uu____27194) ->
                  let head1 =
                    let uu____27196 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____27196
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____27242 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____27242
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____27288 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____27288
                    then
                      let uu____27292 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____27294 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____27296 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____27292 uu____27294 uu____27296
                    else ());
                   (let no_free_uvars t =
                      (let uu____27310 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____27310) &&
                        (let uu____27314 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____27314)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____27331 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____27331 = FStar_Syntax_Util.Equal  in
                    let uu____27332 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____27332
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____27336 = equal t1 t2  in
                         (if uu____27336
                          then
                            let uu____27339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____27339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____27344 =
                            let uu____27351 = equal t1 t2  in
                            if uu____27351
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27364 = mk_eq2 wl env orig t1 t2  in
                               match uu____27364 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____27344 with
                          | (guard,wl1) ->
                              let uu____27385 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____27385))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____27388,uu____27389) ->
                  let head1 =
                    let uu____27407 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____27407
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____27453 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____27453
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____27499 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____27499
                    then
                      let uu____27503 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____27505 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____27507 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____27503 uu____27505 uu____27507
                    else ());
                   (let no_free_uvars t =
                      (let uu____27521 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____27521) &&
                        (let uu____27525 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____27525)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____27542 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____27542 = FStar_Syntax_Util.Equal  in
                    let uu____27543 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____27543
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____27547 = equal t1 t2  in
                         (if uu____27547
                          then
                            let uu____27550 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____27550
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____27555 =
                            let uu____27562 = equal t1 t2  in
                            if uu____27562
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27575 = mk_eq2 wl env orig t1 t2  in
                               match uu____27575 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____27555 with
                          | (guard,wl1) ->
                              let uu____27596 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____27596))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____27599,FStar_Syntax_Syntax.Tm_match uu____27600) ->
                  let head1 =
                    let uu____27624 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____27624
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____27670 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____27670
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____27716 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____27716
                    then
                      let uu____27720 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____27722 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____27724 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____27720 uu____27722 uu____27724
                    else ());
                   (let no_free_uvars t =
                      (let uu____27738 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____27738) &&
                        (let uu____27742 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____27742)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____27759 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____27759 = FStar_Syntax_Util.Equal  in
                    let uu____27760 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____27760
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____27764 = equal t1 t2  in
                         (if uu____27764
                          then
                            let uu____27767 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____27767
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____27772 =
                            let uu____27779 = equal t1 t2  in
                            if uu____27779
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27792 = mk_eq2 wl env orig t1 t2  in
                               match uu____27792 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____27772 with
                          | (guard,wl1) ->
                              let uu____27813 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____27813))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____27816,FStar_Syntax_Syntax.Tm_uinst uu____27817) ->
                  let head1 =
                    let uu____27825 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____27825
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____27865 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____27865
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____27905 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____27905
                    then
                      let uu____27909 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____27911 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____27913 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____27909 uu____27911 uu____27913
                    else ());
                   (let no_free_uvars t =
                      (let uu____27927 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____27927) &&
                        (let uu____27931 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____27931)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____27948 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____27948 = FStar_Syntax_Util.Equal  in
                    let uu____27949 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____27949
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____27953 = equal t1 t2  in
                         (if uu____27953
                          then
                            let uu____27956 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____27956
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____27961 =
                            let uu____27968 = equal t1 t2  in
                            if uu____27968
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27981 = mk_eq2 wl env orig t1 t2  in
                               match uu____27981 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____27961 with
                          | (guard,wl1) ->
                              let uu____28002 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____28002))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____28005,FStar_Syntax_Syntax.Tm_name uu____28006) ->
                  let head1 =
                    let uu____28008 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____28008
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____28048 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____28048
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____28088 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____28088
                    then
                      let uu____28092 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____28094 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____28096 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____28092 uu____28094 uu____28096
                    else ());
                   (let no_free_uvars t =
                      (let uu____28110 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____28110) &&
                        (let uu____28114 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____28114)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____28131 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____28131 = FStar_Syntax_Util.Equal  in
                    let uu____28132 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____28132
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____28136 = equal t1 t2  in
                         (if uu____28136
                          then
                            let uu____28139 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____28139
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____28144 =
                            let uu____28151 = equal t1 t2  in
                            if uu____28151
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____28164 = mk_eq2 wl env orig t1 t2  in
                               match uu____28164 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____28144 with
                          | (guard,wl1) ->
                              let uu____28185 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____28185))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____28188,FStar_Syntax_Syntax.Tm_constant uu____28189) ->
                  let head1 =
                    let uu____28191 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____28191
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____28231 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____28231
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____28271 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____28271
                    then
                      let uu____28275 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____28277 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____28279 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____28275 uu____28277 uu____28279
                    else ());
                   (let no_free_uvars t =
                      (let uu____28293 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____28293) &&
                        (let uu____28297 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____28297)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____28314 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____28314 = FStar_Syntax_Util.Equal  in
                    let uu____28315 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____28315
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____28319 = equal t1 t2  in
                         (if uu____28319
                          then
                            let uu____28322 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____28322
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____28327 =
                            let uu____28334 = equal t1 t2  in
                            if uu____28334
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____28347 = mk_eq2 wl env orig t1 t2  in
                               match uu____28347 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____28327 with
                          | (guard,wl1) ->
                              let uu____28368 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____28368))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____28371,FStar_Syntax_Syntax.Tm_fvar uu____28372) ->
                  let head1 =
                    let uu____28374 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____28374
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____28414 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____28414
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____28454 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____28454
                    then
                      let uu____28458 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____28460 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____28462 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____28458 uu____28460 uu____28462
                    else ());
                   (let no_free_uvars t =
                      (let uu____28476 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____28476) &&
                        (let uu____28480 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____28480)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____28497 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____28497 = FStar_Syntax_Util.Equal  in
                    let uu____28498 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____28498
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____28502 = equal t1 t2  in
                         (if uu____28502
                          then
                            let uu____28505 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____28505
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____28510 =
                            let uu____28517 = equal t1 t2  in
                            if uu____28517
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____28530 = mk_eq2 wl env orig t1 t2  in
                               match uu____28530 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____28510 with
                          | (guard,wl1) ->
                              let uu____28551 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____28551))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____28554,FStar_Syntax_Syntax.Tm_app uu____28555) ->
                  let head1 =
                    let uu____28573 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____28573
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____28613 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____28613
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____28653 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____28653
                    then
                      let uu____28657 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____28659 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____28661 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____28657 uu____28659 uu____28661
                    else ());
                   (let no_free_uvars t =
                      (let uu____28675 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____28675) &&
                        (let uu____28679 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____28679)
                       in
                    let equal t11 t21 =
                      let t12 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____28696 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____28696 = FStar_Syntax_Util.Equal  in
                    let uu____28697 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____28697
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____28701 = equal t1 t2  in
                         (if uu____28701
                          then
                            let uu____28704 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____28704
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____28709 =
                            let uu____28716 = equal t1 t2  in
                            if uu____28716
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____28729 = mk_eq2 wl env orig t1 t2  in
                               match uu____28729 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____28709 with
                          | (guard,wl1) ->
                              let uu____28750 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____28750))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____28753,FStar_Syntax_Syntax.Tm_let uu____28754) ->
                  let uu____28781 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____28781
                  then
                    let uu____28784 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____28784
                  else giveup env "Tm_let mismatch (%s-%s vs %s-%s)" orig
              | (FStar_Syntax_Syntax.Tm_let uu____28788,uu____28789) ->
                  let uu____28803 =
                    let uu____28809 =
                      let uu____28811 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____28813 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____28815 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____28817 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____28811 uu____28813 uu____28815 uu____28817
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____28809)
                     in
                  FStar_Errors.raise_error uu____28803
                    t1.FStar_Syntax_Syntax.pos
              | (uu____28821,FStar_Syntax_Syntax.Tm_let uu____28822) ->
                  let uu____28836 =
                    let uu____28842 =
                      let uu____28844 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____28846 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____28848 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____28850 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____28844 uu____28846 uu____28848 uu____28850
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____28842)
                     in
                  FStar_Errors.raise_error uu____28836
                    t1.FStar_Syntax_Syntax.pos
              | uu____28854 -> giveup env "head tag mismatch" orig))))

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
        let solve_eq c1_comp c2_comp =
          (let uu____28918 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____28918
           then
             let uu____28923 =
               let uu____28925 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____28925  in
             let uu____28926 =
               let uu____28928 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____28928  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____28923 uu____28926
           else ());
          (let uu____28932 =
             let uu____28934 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____28934  in
           if uu____28932
           then
             let uu____28937 =
               let uu____28939 =
                 FStar_Syntax_Print.lid_to_string
                   c1_comp.FStar_Syntax_Syntax.effect_name
                  in
               let uu____28941 =
                 FStar_Syntax_Print.lid_to_string
                   c2_comp.FStar_Syntax_Syntax.effect_name
                  in
               FStar_Util.format2 "incompatible effects: %s <> %s"
                 uu____28939 uu____28941
                in
             giveup env uu____28937 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____28963 =
                  let uu____28965 =
                    FStar_Syntax_Print.args_to_string
                      c1_comp.FStar_Syntax_Syntax.effect_args
                     in
                  let uu____28967 =
                    FStar_Syntax_Print.args_to_string
                      c2_comp.FStar_Syntax_Syntax.effect_args
                     in
                  FStar_Util.format2
                    "incompatible effect arguments: %s <> %s" uu____28965
                    uu____28967
                   in
                giveup env uu____28963 orig)
             else
               (let uu____28972 =
                  sub_prob wl c1_comp.FStar_Syntax_Syntax.result_typ
                    FStar_TypeChecker_Common.EQ
                    c2_comp.FStar_Syntax_Syntax.result_typ "effect ret type"
                   in
                match uu____28972 with
                | (ret_sub_prob,wl1) ->
                    let uu____28980 =
                      FStar_List.fold_right2
                        (fun uu____29017  ->
                           fun uu____29018  ->
                             fun uu____29019  ->
                               match (uu____29017, uu____29018, uu____29019)
                               with
                               | ((a1,uu____29063),(a2,uu____29065),(arg_sub_probs,wl2))
                                   ->
                                   let uu____29098 =
                                     sub_prob wl2 a1
                                       FStar_TypeChecker_Common.EQ a2
                                       "effect arg"
                                      in
                                   (match uu____29098 with
                                    | (p,wl3) -> ((p :: arg_sub_probs), wl3)))
                        c1_comp.FStar_Syntax_Syntax.effect_args
                        c2_comp.FStar_Syntax_Syntax.effect_args ([], wl1)
                       in
                    (match uu____28980 with
                     | (arg_sub_probs,wl2) ->
                         let sub_probs = ret_sub_prob :: arg_sub_probs  in
                         let guard =
                           let uu____29128 = FStar_List.map p_guard sub_probs
                              in
                           FStar_Syntax_Util.mk_conj_l uu____29128  in
                         let wl3 =
                           solve_prob orig
                             (FStar_Pervasives_Native.Some guard) [] wl2
                            in
                         let uu____29136 = attempt sub_probs wl3  in
                         solve env uu____29136)))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____29159 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____29162)::[] -> wp1
              | uu____29187 ->
                  let uu____29198 =
                    let uu____29200 =
                      let uu____29202 =
                        FStar_Ident.range_of_lid
                          c11.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Range.string_of_range uu____29202  in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____29200
                     in
                  failwith uu____29198
               in
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____29209 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____29209]
              | x -> x  in
            let uu____29211 =
              let uu____29222 =
                let uu____29231 =
                  let uu____29232 = FStar_List.hd univs1  in
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    uu____29232 c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____29231  in
              [uu____29222]  in
            {
              FStar_Syntax_Syntax.comp_univs = univs1;
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____29211;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____29250 = lift_c1 ()  in solve_eq uu____29250 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___31_29259  ->
                       match uu___31_29259 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____29264 -> false))
                in
             let uu____29266 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____29296)::uu____29297,(wp2,uu____29299)::uu____29300)
                   -> (wp1, wp2)
               | uu____29373 ->
                   let uu____29398 =
                     let uu____29404 =
                       let uu____29406 =
                         FStar_Syntax_Print.lid_to_string
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____29408 =
                         FStar_Syntax_Print.lid_to_string
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         uu____29406 uu____29408
                        in
                     (FStar_Errors.Fatal_ExpectNormalizedEffect, uu____29404)
                      in
                   FStar_Errors.raise_error uu____29398
                     env.FStar_TypeChecker_Env.range
                in
             match uu____29266 with
             | (wpc1,wpc2) ->
                 let uu____29418 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____29418
                 then
                   let uu____29423 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____29423 wl
                 else
                   (let uu____29427 =
                      let uu____29434 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____29434  in
                    match uu____29427 with
                    | (c2_decl,qualifiers) ->
                        let uu____29455 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____29455
                        then
                          let c1_repr =
                            let uu____29462 =
                              let uu____29463 =
                                let uu____29464 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____29464  in
                              let uu____29465 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____29463 uu____29465
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____29462
                             in
                          let c2_repr =
                            let uu____29467 =
                              let uu____29468 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____29469 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____29468 uu____29469
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.UnfoldUntil
                                 FStar_Syntax_Syntax.delta_constant;
                              FStar_TypeChecker_Env.Weak;
                              FStar_TypeChecker_Env.HNF] env uu____29467
                             in
                          let uu____29470 =
                            let uu____29475 =
                              let uu____29477 =
                                FStar_Syntax_Print.term_to_string c1_repr  in
                              let uu____29479 =
                                FStar_Syntax_Print.term_to_string c2_repr  in
                              FStar_Util.format2 "sub effect repr: %s <: %s"
                                uu____29477 uu____29479
                               in
                            sub_prob wl c1_repr
                              problem.FStar_TypeChecker_Common.relation
                              c2_repr uu____29475
                             in
                          (match uu____29470 with
                           | (prob,wl1) ->
                               let wl2 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some
                                      (p_guard prob)) [] wl1
                                  in
                               let uu____29485 = attempt [prob] wl2  in
                               solve env uu____29485)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____29500 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____29500
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let c1_univ =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env c11.FStar_Syntax_Syntax.result_typ
                                      in
                                   let uu____29509 =
                                     let uu____29516 =
                                       let uu____29517 =
                                         let uu____29534 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____29537 =
                                           let uu____29548 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____29557 =
                                             let uu____29568 =
                                               let uu____29577 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c1_univ
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____29577
                                                in
                                             [uu____29568]  in
                                           uu____29548 :: uu____29557  in
                                         (uu____29534, uu____29537)  in
                                       FStar_Syntax_Syntax.Tm_app uu____29517
                                        in
                                     FStar_Syntax_Syntax.mk uu____29516  in
                                   uu____29509 FStar_Pervasives_Native.None r))
                               else
                                 (let c1_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  let c2_univ =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  let uu____29626 =
                                    let uu____29633 =
                                      let uu____29634 =
                                        let uu____29651 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____29654 =
                                          let uu____29665 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____29674 =
                                            let uu____29685 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____29694 =
                                              let uu____29705 =
                                                let uu____29714 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c1_univ
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____29714
                                                 in
                                              [uu____29705]  in
                                            uu____29685 :: uu____29694  in
                                          uu____29665 :: uu____29674  in
                                        (uu____29651, uu____29654)  in
                                      FStar_Syntax_Syntax.Tm_app uu____29634
                                       in
                                    FStar_Syntax_Syntax.mk uu____29633  in
                                  uu____29626 FStar_Pervasives_Native.None r)
                              in
                           (let uu____29768 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29768
                            then
                              let uu____29773 =
                                let uu____29775 =
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Iota;
                                    FStar_TypeChecker_Env.Eager_unfolding;
                                    FStar_TypeChecker_Env.Primops;
                                    FStar_TypeChecker_Env.Simplify] env g
                                   in
                                FStar_Syntax_Print.term_to_string uu____29775
                                 in
                              FStar_Util.print1
                                "WP guard (simplifed) is (%s)\n" uu____29773
                            else ());
                           (let uu____29779 =
                              sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                problem.FStar_TypeChecker_Common.relation
                                c21.FStar_Syntax_Syntax.result_typ
                                "result type"
                               in
                            match uu____29779 with
                            | (base_prob,wl1) ->
                                let wl2 =
                                  let uu____29788 =
                                    let uu____29791 =
                                      FStar_Syntax_Util.mk_conj
                                        (p_guard base_prob) g
                                       in
                                    FStar_All.pipe_left
                                      (fun _29794  ->
                                         FStar_Pervasives_Native.Some _29794)
                                      uu____29791
                                     in
                                  solve_prob orig uu____29788 [] wl1  in
                                let uu____29795 = attempt [base_prob] wl2  in
                                solve env uu____29795))))
           in
        let uu____29796 = FStar_Util.physical_equality c1 c2  in
        if uu____29796
        then
          let uu____29799 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29799
        else
          ((let uu____29803 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29803
            then
              let uu____29808 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29810 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29808
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29810
            else ());
           (let uu____29815 =
              let uu____29824 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29827 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29824, uu____29827)  in
            match uu____29815 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29845),FStar_Syntax_Syntax.Total
                    (t2,uu____29847)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____29864 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29864 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29866,FStar_Syntax_Syntax.Total uu____29867) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29886),FStar_Syntax_Syntax.Total
                    (t2,uu____29888)) ->
                     let uu____29905 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29905 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29908),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29910)) ->
                     let uu____29927 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29927 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29930),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29932)) ->
                     if
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.SUB
                     then
                       let uu____29950 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29950 wl
                     else giveup env "GTot =/= Tot" orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29955,FStar_Syntax_Syntax.Comp uu____29956) ->
                     let uu____29965 =
                       let uu___3696_29968 = problem  in
                       let uu____29971 =
                         let uu____29972 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29972
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3696_29968.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29971;
                         FStar_TypeChecker_Common.relation =
                           (uu___3696_29968.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3696_29968.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3696_29968.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3696_29968.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3696_29968.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3696_29968.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3696_29968.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3696_29968.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29965 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29973,FStar_Syntax_Syntax.Comp uu____29974) ->
                     let uu____29983 =
                       let uu___3696_29986 = problem  in
                       let uu____29989 =
                         let uu____29990 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29990
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3696_29986.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29989;
                         FStar_TypeChecker_Common.relation =
                           (uu___3696_29986.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3696_29986.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3696_29986.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3696_29986.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3696_29986.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3696_29986.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3696_29986.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3696_29986.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29983 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29991,FStar_Syntax_Syntax.GTotal uu____29992) ->
                     let uu____30001 =
                       let uu___3708_30004 = problem  in
                       let uu____30007 =
                         let uu____30008 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____30008
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3708_30004.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3708_30004.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3708_30004.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____30007;
                         FStar_TypeChecker_Common.element =
                           (uu___3708_30004.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3708_30004.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3708_30004.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3708_30004.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3708_30004.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3708_30004.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____30001 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____30009,FStar_Syntax_Syntax.Total uu____30010) ->
                     let uu____30019 =
                       let uu___3708_30022 = problem  in
                       let uu____30025 =
                         let uu____30026 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____30026
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3708_30022.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3708_30022.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3708_30022.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____30025;
                         FStar_TypeChecker_Common.element =
                           (uu___3708_30022.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3708_30022.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3708_30022.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3708_30022.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3708_30022.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3708_30022.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____30019 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____30027,FStar_Syntax_Syntax.Comp uu____30028) ->
                     let uu____30029 =
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
                     if uu____30029
                     then
                       let uu____30032 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____30032 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____30039 =
                            let uu____30044 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____30044
                            then (c1_comp, c2_comp)
                            else
                              (let uu____30053 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____30054 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____30053, uu____30054))
                             in
                          match uu____30039 with
                          | (c1_comp1,c2_comp1) -> solve_eq c1_comp1 c2_comp1
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____30062 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____30062
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____30070 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____30070 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____30073 =
                                  let uu____30075 =
                                    FStar_Syntax_Print.lid_to_string
                                      c12.FStar_Syntax_Syntax.effect_name
                                     in
                                  let uu____30077 =
                                    FStar_Syntax_Print.lid_to_string
                                      c22.FStar_Syntax_Syntax.effect_name
                                     in
                                  FStar_Util.format2
                                    "incompatible monad ordering: %s </: %s"
                                    uu____30075 uu____30077
                                   in
                                giveup env uu____30073 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun g  ->
    let uu____30088 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Env.imp_tm))
       in
    FStar_All.pipe_right uu____30088 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____30138 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____30138 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____30163 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____30194  ->
                match uu____30194 with
                | (u1,u2) ->
                    let uu____30202 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____30204 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____30202 uu____30204))
         in
      FStar_All.pipe_right uu____30163 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____30241,[])) when
          let uu____30268 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30268 -> "{}"
      | uu____30271 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30298 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30298
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____30310 =
              FStar_List.map
                (fun uu____30323  ->
                   match uu____30323 with
                   | (uu____30330,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____30310 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30341 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____30341 imps
  
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
                  let uu____30398 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30398
                  then
                    let uu____30406 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30408 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30406
                      (rel_to_string rel) uu____30408
                  else "TOP"  in
                let uu____30414 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30414 with
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
              let uu____30474 =
                let uu____30477 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30480  -> FStar_Pervasives_Native.Some _30480)
                  uu____30477
                 in
              FStar_Syntax_Syntax.new_bv uu____30474 t1  in
            let uu____30481 =
              let uu____30486 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30486
               in
            match uu____30481 with | (p,wl1) -> (p, x, wl1)
  
let (solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         (FStar_TypeChecker_Common.deferred *
           FStar_TypeChecker_Env.implicits) FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicits)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____30546 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30546
         then
           let uu____30551 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30551
         else ());
        (let uu____30558 =
           FStar_Util.record_time (fun uu____30565  -> solve env probs)  in
         match uu____30558 with
         | (sol,ms) ->
             ((let uu____30577 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30577
               then
                 let uu____30582 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30582
               else ());
              (match sol with
               | Success (deferred,implicits) ->
                   let uu____30595 =
                     FStar_Util.record_time
                       (fun uu____30602  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30595 with
                    | ((),ms1) ->
                        ((let uu____30613 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30613
                          then
                            let uu____30618 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30618
                          else ());
                         FStar_Pervasives_Native.Some (deferred, implicits)))
               | Failed (d,s) ->
                   ((let uu____30632 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30632
                     then
                       let uu____30639 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30639
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____30666 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30666
            then
              let uu____30671 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30671
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30678 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30678
             then
               let uu____30683 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30683
             else ());
            (let f2 =
               let uu____30689 =
                 let uu____30690 = FStar_Syntax_Util.unmeta f1  in
                 uu____30690.FStar_Syntax_Syntax.n  in
               match uu____30689 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30694 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___3824_30695 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___3824_30695.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___3824_30695.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___3824_30695.FStar_TypeChecker_Env.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Env.implicit
        Prims.list) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,implicits) ->
            let uu____30750 =
              let uu____30751 =
                let uu____30752 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30753  ->
                       FStar_TypeChecker_Common.NonTrivial _30753)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____30752;
                  FStar_TypeChecker_Env.deferred = deferred;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = implicits
                }  in
              simplify_guard env uu____30751  in
            FStar_All.pipe_left
              (fun _30760  -> FStar_Pervasives_Native.Some _30760)
              uu____30750
  
let with_guard_no_simp :
  'Auu____30770 .
    'Auu____30770 ->
      FStar_TypeChecker_Common.prob ->
        FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some d ->
            let uu____30793 =
              let uu____30794 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30795  -> FStar_TypeChecker_Common.NonTrivial _30795)
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____30794;
                FStar_TypeChecker_Env.deferred = d;
                FStar_TypeChecker_Env.univ_ineqs = ([], []);
                FStar_TypeChecker_Env.implicits = []
              }  in
            FStar_Pervasives_Native.Some uu____30793
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____30828 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30828
           then
             let uu____30833 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30835 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30833
               uu____30835
           else ());
          (let uu____30840 =
             let uu____30845 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30845
              in
           match uu____30840 with
           | (prob,wl) ->
               let g =
                 let uu____30853 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30863  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30853  in
               ((let uu____30884 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30884
                 then
                   let uu____30889 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30889
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30910 = try_teq true env t1 t2  in
        match uu____30910 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30915 = FStar_TypeChecker_Env.get_range env  in
              let uu____30916 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30915 uu____30916);
             FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30924 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30924
              then
                let uu____30929 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30931 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30933 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30929
                  uu____30931 uu____30933
              else ());
             g)
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30959 = FStar_TypeChecker_Env.get_range env  in
          let uu____30960 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30959 uu____30960
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30989 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30989
         then
           let uu____30994 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30996 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30994 uu____30996
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____31007 =
           let uu____31014 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____31014 "sub_comp"
            in
         match uu____31007 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____31027 =
                 FStar_Util.record_time
                   (fun uu____31039  ->
                      let uu____31040 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____31051  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____31040)
                  in
               match uu____31027 with
               | (r,ms) ->
                   ((let uu____31082 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____31082
                     then
                       let uu____31087 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____31089 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____31091 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31087 uu____31089
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31091
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
      fun uu____31129  ->
        match uu____31129 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31172 =
                 let uu____31178 =
                   let uu____31180 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31182 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31180 uu____31182
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31178)  in
               let uu____31186 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31172 uu____31186)
               in
            let equiv1 v1 v' =
              let uu____31199 =
                let uu____31204 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31205 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31204, uu____31205)  in
              match uu____31199 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31225 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31256 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31256 with
                      | FStar_Syntax_Syntax.U_unif uu____31263 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31292  ->
                                    match uu____31292 with
                                    | (u,v') ->
                                        let uu____31301 = equiv1 v1 v'  in
                                        if uu____31301
                                        then
                                          let uu____31306 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31306 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31327 -> []))
               in
            let uu____31332 =
              let wl =
                let uu___3917_31336 = empty_worklist env  in
                {
                  attempting = (uu___3917_31336.attempting);
                  wl_deferred = (uu___3917_31336.wl_deferred);
                  ctr = (uu___3917_31336.ctr);
                  defer_ok = false;
                  smt_ok = (uu___3917_31336.smt_ok);
                  umax_heuristic_ok = (uu___3917_31336.umax_heuristic_ok);
                  tcenv = (uu___3917_31336.tcenv);
                  wl_implicits = (uu___3917_31336.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31355  ->
                      match uu____31355 with
                      | (lb,v1) ->
                          let uu____31362 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31362 with
                           | USolved wl1 -> ()
                           | uu____31365 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31376 =
              match uu____31376 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31388) -> true
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
                      uu____31412,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31414,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31425) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31433,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31442 -> false)
               in
            let uu____31448 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31465  ->
                      match uu____31465 with
                      | (u,v1) ->
                          let uu____31473 = check_ineq (u, v1)  in
                          if uu____31473
                          then true
                          else
                            ((let uu____31481 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31481
                              then
                                let uu____31486 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31488 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31486
                                  uu____31488
                              else ());
                             false)))
               in
            if uu____31448
            then ()
            else
              ((let uu____31498 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31498
                then
                  ((let uu____31504 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31504);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31516 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31516))
                else ());
               (let uu____31529 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31529))
  
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
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____31603 =
          match uu____31603 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___3994_31629 =
            wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
          {
            attempting = (uu___3994_31629.attempting);
            wl_deferred = (uu___3994_31629.wl_deferred);
            ctr = (uu___3994_31629.ctr);
            defer_ok;
            smt_ok = (uu___3994_31629.smt_ok);
            umax_heuristic_ok = (uu___3994_31629.umax_heuristic_ok);
            tcenv = (uu___3994_31629.tcenv);
            wl_implicits = (uu___3994_31629.wl_implicits)
          }  in
        (let uu____31632 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31632
         then
           let uu____31637 = FStar_Util.string_of_bool defer_ok  in
           let uu____31639 = wl_to_string wl  in
           let uu____31641 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31637 uu____31639 uu____31641
         else ());
        (let g1 =
           let uu____31647 = solve_and_commit env wl fail1  in
           match uu____31647 with
           | FStar_Pervasives_Native.Some
               (uu____31654::uu____31655,uu____31656) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,imps) ->
               let uu___4009_31685 = g  in
               {
                 FStar_TypeChecker_Env.guard_f =
                   (uu___4009_31685.FStar_TypeChecker_Env.guard_f);
                 FStar_TypeChecker_Env.deferred = deferred;
                 FStar_TypeChecker_Env.univ_ineqs =
                   (uu___4009_31685.FStar_TypeChecker_Env.univ_ineqs);
                 FStar_TypeChecker_Env.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Env.implicits imps)
               }
           | uu____31686 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
         (let uu___4014_31695 = g1  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4014_31695.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4014_31695.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs = ([], []);
            FStar_TypeChecker_Env.implicits =
              (uu___4014_31695.FStar_TypeChecker_Env.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
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
            let uu___4026_31772 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___4026_31772.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___4026_31772.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___4026_31772.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____31773 =
            let uu____31775 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____31775  in
          if uu____31773
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 (if debug1
                  then
                    (let uu____31787 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____31788 =
                       let uu____31790 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____31790
                        in
                     FStar_Errors.diag uu____31787 uu____31788)
                  else ();
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Env.Eager_unfolding;
                       FStar_TypeChecker_Env.Simplify;
                       FStar_TypeChecker_Env.Primops] env vc
                      in
                   if debug1
                   then
                     (let uu____31798 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31799 =
                        let uu____31801 =
                          FStar_Syntax_Print.term_to_string vc1  in
                        FStar_Util.format1 "After normalization VC=\n%s\n"
                          uu____31801
                         in
                      FStar_Errors.diag uu____31798 uu____31799)
                   else ();
                   (let uu____31807 = FStar_TypeChecker_Env.get_range env  in
                    FStar_TypeChecker_Env.def_check_closed_in_env uu____31807
                      "discharge_guard'" env vc1);
                   (let uu____31809 = FStar_TypeChecker_Env.check_trivial vc1
                       in
                    match uu____31809 with
                    | FStar_TypeChecker_Common.Trivial  ->
                        FStar_Pervasives_Native.Some ret_g
                    | FStar_TypeChecker_Common.NonTrivial vc2 ->
                        if Prims.op_Negation use_smt
                        then
                          (if debug1
                           then
                             (let uu____31818 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31819 =
                                let uu____31821 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1
                                  "Cannot solve without SMT : %s\n"
                                  uu____31821
                                 in
                              FStar_Errors.diag uu____31818 uu____31819)
                           else ();
                           FStar_Pervasives_Native.None)
                        else
                          (if debug1
                           then
                             (let uu____31831 =
                                FStar_TypeChecker_Env.get_range env  in
                              let uu____31832 =
                                let uu____31834 =
                                  FStar_Syntax_Print.term_to_string vc2  in
                                FStar_Util.format1 "Checking VC=\n%s\n"
                                  uu____31834
                                 in
                              FStar_Errors.diag uu____31831 uu____31832)
                           else ();
                           (let vcs =
                              let uu____31848 = FStar_Options.use_tactics ()
                                 in
                              if uu____31848
                              then
                                FStar_Options.with_saved_options
                                  (fun uu____31870  ->
                                     (let uu____31872 =
                                        FStar_Options.set_options
                                          "--no_tactics"
                                         in
                                      FStar_All.pipe_left (fun a1  -> ())
                                        uu____31872);
                                     (let vcs =
                                        (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                          env vc2
                                         in
                                      FStar_All.pipe_right vcs
                                        (FStar_List.map
                                           (fun uu____31916  ->
                                              match uu____31916 with
                                              | (env1,goal,opts) ->
                                                  let uu____31932 =
                                                    FStar_TypeChecker_Normalize.normalize
                                                      [FStar_TypeChecker_Env.Simplify;
                                                      FStar_TypeChecker_Env.Primops]
                                                      env1 goal
                                                     in
                                                  (env1, uu____31932, opts)))))
                              else
                                (let uu____31935 =
                                   let uu____31942 = FStar_Options.peek ()
                                      in
                                   (env, vc2, uu____31942)  in
                                 [uu____31935])
                               in
                            FStar_All.pipe_right vcs
                              (FStar_List.iter
                                 (fun uu____31975  ->
                                    match uu____31975 with
                                    | (env1,goal,opts) ->
                                        let uu____31985 =
                                          FStar_TypeChecker_Env.check_trivial
                                            goal
                                           in
                                        (match uu____31985 with
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
                                                (let uu____31996 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____31997 =
                                                   let uu____31999 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   let uu____32001 =
                                                     FStar_TypeChecker_Env.string_of_proof_ns
                                                       env1
                                                      in
                                                   FStar_Util.format2
                                                     "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                     uu____31999 uu____32001
                                                    in
                                                 FStar_Errors.diag
                                                   uu____31996 uu____31997)
                                              else ();
                                              if debug1
                                              then
                                                (let uu____32008 =
                                                   FStar_TypeChecker_Env.get_range
                                                     env1
                                                    in
                                                 let uu____32009 =
                                                   let uu____32011 =
                                                     FStar_Syntax_Print.term_to_string
                                                       goal1
                                                      in
                                                   FStar_Util.format1
                                                     "Before calling solver VC=\n%s\n"
                                                     uu____32011
                                                    in
                                                 FStar_Errors.diag
                                                   uu____32008 uu____32009)
                                              else ();
                                              (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                use_env_range_msg env1 goal1;
                                              FStar_Options.pop ())))));
                           FStar_Pervasives_Native.Some ret_g)))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32029 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____32029 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____32038 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32038
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32052 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____32052 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32082 = try_teq false env t1 t2  in
        match uu____32082 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____32126 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32126 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32139 ->
                     let uu____32152 =
                       let uu____32153 = FStar_Syntax_Subst.compress r  in
                       uu____32153.FStar_Syntax_Syntax.n  in
                     (match uu____32152 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32158) ->
                          unresolved ctx_u'
                      | uu____32175 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32199 = acc  in
            match uu____32199 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32218 = hd1  in
                     (match uu____32218 with
                      | { FStar_TypeChecker_Env.imp_reason = reason;
                          FStar_TypeChecker_Env.imp_uvar = ctx_u;
                          FStar_TypeChecker_Env.imp_tm = tm;
                          FStar_TypeChecker_Env.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32229 = unresolved ctx_u  in
                             if uu____32229
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.None  ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                               | FStar_Pervasives_Native.Some (env_dyn,tau)
                                   ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32253 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32253
                                     then
                                       let uu____32257 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32257
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32266 = teq_nosmt env1 t tm
                                          in
                                       match uu____32266 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Env.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4138_32276 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4138_32276.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4141_32284 = hd1  in
                                       {
                                         FStar_TypeChecker_Env.imp_reason =
                                           (uu___4141_32284.FStar_TypeChecker_Env.imp_reason);
                                         FStar_TypeChecker_Env.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Env.imp_tm =
                                           (uu___4141_32284.FStar_TypeChecker_Env.imp_tm);
                                         FStar_TypeChecker_Env.imp_range =
                                           (uu___4141_32284.FStar_TypeChecker_Env.imp_range)
                                       }  in
                                     until_fixpoint (out, true) (hd2 ::
                                       (FStar_List.append extra tl1))))
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4145_32295 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4145_32295.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4145_32295.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4145_32295.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4145_32295.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4145_32295.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4145_32295.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4145_32295.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4145_32295.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4145_32295.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4145_32295.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4145_32295.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4145_32295.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4145_32295.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4145_32295.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4145_32295.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4145_32295.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4145_32295.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4145_32295.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4145_32295.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4145_32295.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4145_32295.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4145_32295.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4145_32295.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4145_32295.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4145_32295.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4145_32295.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4145_32295.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4145_32295.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4145_32295.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4145_32295.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4145_32295.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4145_32295.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4145_32295.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4145_32295.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4145_32295.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4145_32295.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4145_32295.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4145_32295.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4145_32295.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4145_32295.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4145_32295.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4145_32295.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4145_32295.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4145_32295.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  let tm1 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4150_32299 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4150_32299.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4150_32299.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4150_32299.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4150_32299.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4150_32299.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4150_32299.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4150_32299.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4150_32299.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4150_32299.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4150_32299.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4150_32299.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4150_32299.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4150_32299.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4150_32299.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4150_32299.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4150_32299.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4150_32299.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4150_32299.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4150_32299.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4150_32299.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4150_32299.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4150_32299.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4150_32299.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4150_32299.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4150_32299.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4150_32299.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4150_32299.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4150_32299.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4150_32299.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4150_32299.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4150_32299.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4150_32299.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4150_32299.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4150_32299.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4150_32299.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4150_32299.FStar_TypeChecker_Env.erasable_types_tab)
                                      }
                                    else env1  in
                                  (let uu____32304 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32304
                                   then
                                     let uu____32309 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32311 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32313 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32315 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32309 uu____32311 uu____32313
                                       reason uu____32315
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4156_32322  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32329 =
                                             let uu____32339 =
                                               let uu____32347 =
                                                 let uu____32349 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32351 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32353 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32349 uu____32351
                                                   uu____32353
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32347, r)
                                                in
                                             [uu____32339]  in
                                           FStar_Errors.add_errors
                                             uu____32329);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32372 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32383  ->
                                               let uu____32384 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32386 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32388 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32384 uu____32386
                                                 reason uu____32388)) env2 g1
                                         true
                                        in
                                     match uu____32372 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Env.implicits
                                         out), true) tl1)))))
             in
          let uu___4168_32396 = g  in
          let uu____32397 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
          {
            FStar_TypeChecker_Env.guard_f =
              (uu___4168_32396.FStar_TypeChecker_Env.guard_f);
            FStar_TypeChecker_Env.deferred =
              (uu___4168_32396.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___4168_32396.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits = uu____32397
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun g  ->
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> unit) =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____32439 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____32439 (resolve_implicits env)  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____32440 = discharge_guard env g1  in
          FStar_All.pipe_left (fun a2  -> ()) uu____32440
      | imp::uu____32442 ->
          let uu____32445 =
            let uu____32451 =
              let uu____32453 =
                FStar_Syntax_Print.uvar_to_string
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                 in
              let uu____32455 =
                FStar_TypeChecker_Normalize.term_to_string env
                  (imp.FStar_TypeChecker_Env.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                 in
              FStar_Util.format3
                "Failed to resolve implicit argument %s of type %s introduced for %s"
                uu____32453 uu____32455 imp.FStar_TypeChecker_Env.imp_reason
               in
            (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32451)
             in
          FStar_Errors.raise_error uu____32445
            imp.FStar_TypeChecker_Env.imp_range
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32477 = teq_nosmt env t1 t2  in
        match uu____32477 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4190_32496 = FStar_TypeChecker_Env.trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___4190_32496.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___4190_32496.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___4190_32496.FStar_TypeChecker_Env.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32532 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32532
         then
           let uu____32537 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32539 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32537
             uu____32539
         else ());
        (let uu____32544 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32544 with
         | (prob,x,wl) ->
             let g =
               let uu____32563 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32574  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32563  in
             ((let uu____32595 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32595
               then
                 let uu____32600 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32602 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32604 =
                   let uu____32606 = FStar_Util.must g  in
                   guard_to_string env uu____32606  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32600 uu____32602 uu____32604
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
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32643 = check_subtyping env t1 t2  in
        match uu____32643 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32662 =
              let uu____32663 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32663 g  in
            FStar_Pervasives_Native.Some uu____32662
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32682 = check_subtyping env t1 t2  in
        match uu____32682 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32701 =
              let uu____32702 =
                let uu____32703 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32703]  in
              FStar_TypeChecker_Env.close_guard env uu____32702 g  in
            FStar_Pervasives_Native.Some uu____32701
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32741 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32741
         then
           let uu____32746 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32748 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32746
             uu____32748
         else ());
        (let uu____32753 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32753 with
         | (prob,x,wl) ->
             let g =
               let uu____32768 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32779  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32768  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32803 =
                      let uu____32804 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32804]  in
                    FStar_TypeChecker_Env.close_guard env uu____32803 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32845 = subtype_nosmt env t1 t2  in
        match uu____32845 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  