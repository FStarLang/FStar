open Prims
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14 = FStar_Syntax_Util.type_u ()  in
        match uu____14 with
        | (t_type,u) ->
            let uu____19 =
              let uu____22 = FStar_TypeChecker_Env.all_binders env  in
              FStar_TypeChecker_Env.new_uvar t1.FStar_Syntax_Syntax.pos
                uu____22 t_type
               in
            (match uu____19 with
             | (tt,uu____24) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____45 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____71 -> false
  
let __proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob * Prims.string) 
let uu___is_Success : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____151 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____165 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____182 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____186 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____190 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___100_201  ->
    match uu___100_201 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____214 =
    let uu____215 = FStar_Syntax_Subst.compress t  in
    uu____215.FStar_Syntax_Syntax.n  in
  match uu____214 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____232 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____236 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____232 uu____236
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____239;
         FStar_Syntax_Syntax.pos = uu____240;
         FStar_Syntax_Syntax.vars = uu____241;_},args)
      ->
      let uu____269 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____273 = FStar_Syntax_Print.term_to_string ty  in
      let uu____274 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____269 uu____273 uu____274
  | uu____275 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___101_281  ->
      match uu___101_281 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____285 =
            let uu____287 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____288 =
              let uu____290 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____291 =
                let uu____293 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____294 =
                  let uu____296 =
                    let uu____298 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____299 =
                      let uu____301 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____302 =
                        let uu____304 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____305 =
                          let uu____307 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____307]  in
                        uu____304 :: uu____305  in
                      uu____301 :: uu____302  in
                    uu____298 :: uu____299  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____296
                   in
                uu____293 :: uu____294  in
              uu____290 :: uu____291  in
            uu____287 :: uu____288  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____285
      | FStar_TypeChecker_Common.CProb p ->
          let uu____312 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____313 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____312
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____313
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___102_319  ->
      match uu___102_319 with
      | UNIV (u,t) ->
          let x =
            let uu____323 = FStar_Options.hide_uvar_nums ()  in
            if uu____323
            then "?"
            else
              (let uu____325 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____325 FStar_Util.string_of_int)
             in
          let uu____327 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____327
      | TERM ((u,uu____329),t) ->
          let x =
            let uu____334 = FStar_Options.hide_uvar_nums ()  in
            if uu____334
            then "?"
            else
              (let uu____336 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____336 FStar_Util.string_of_int)
             in
          let uu____340 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____340
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____349 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____349 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____357 =
      let uu____359 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____359
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____357 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____377 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____385  ->
            match uu____385 with
            | (x,uu____389) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____377 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____394 =
      let uu____395 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____395  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____394;
      smt_ok = true;
      tcenv = env
    }
  
let singleton' :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___128_408 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___128_408.wl_deferred);
          ctr = (uu___128_408.ctr);
          defer_ok = (uu___128_408.defer_ok);
          smt_ok;
          tcenv = (uu___128_408.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___129_433 = empty_worklist env  in
  let uu____434 = FStar_List.map Prims.snd g  in
  {
    attempting = uu____434;
    wl_deferred = (uu___129_433.wl_deferred);
    ctr = (uu___129_433.ctr);
    defer_ok = false;
    smt_ok = (uu___129_433.smt_ok);
    tcenv = (uu___129_433.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___130_446 = wl  in
        {
          attempting = (uu___130_446.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___130_446.ctr);
          defer_ok = (uu___130_446.defer_ok);
          smt_ok = (uu___130_446.smt_ok);
          tcenv = (uu___130_446.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___131_458 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___131_458.wl_deferred);
        ctr = (uu___131_458.ctr);
        defer_ok = (uu___131_458.defer_ok);
        smt_ok = (uu___131_458.smt_ok);
        tcenv = (uu___131_458.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____469 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____469
         then
           let uu____470 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____470
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___103_474  ->
    match uu___103_474 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___132_490 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___132_490.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___132_490.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___132_490.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___132_490.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___132_490.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___132_490.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___132_490.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___104_511  ->
    match uu___104_511 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_28  -> FStar_TypeChecker_Common.TProb _0_28)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_29  -> FStar_TypeChecker_Common.CProb _0_29)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___105_527  ->
      match uu___105_527 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___106_530  ->
    match uu___106_530 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___107_539  ->
    match uu___107_539 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___108_549  ->
    match uu___108_549 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___109_559  ->
    match uu___109_559 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___110_570  ->
    match uu___110_570 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___111_581  ->
    match uu___111_581 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___112_590  ->
    match uu___112_590 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_30  -> FStar_TypeChecker_Common.TProb _0_30) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_31  -> FStar_TypeChecker_Common.CProb _0_31) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____604 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____604 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____615  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____665 = next_pid ()  in
  let uu____666 =
    FStar_TypeChecker_Env.new_uvar FStar_Range.dummyRange scope
      FStar_Syntax_Util.ktype0
     in
  {
    FStar_TypeChecker_Common.pid = uu____665;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____666;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____713 = next_pid ()  in
  let uu____714 =
    FStar_TypeChecker_Env.new_uvar FStar_Range.dummyRange scope
      FStar_Syntax_Util.ktype0
     in
  {
    FStar_TypeChecker_Common.pid = uu____713;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____714;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____755 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____755;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = (p_guard orig);
    FStar_TypeChecker_Common.scope = (p_scope orig);
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let guard_on_element problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | None  -> FStar_Syntax_Util.mk_forall x phi
  | Some e -> FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi 
let explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____801 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____801
        then
          let uu____802 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____803 = prob_to_string env d  in
          let uu____804 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____802 uu____803 uu____804 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____809 -> failwith "impossible"  in
           let uu____810 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____818 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____819 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____818, uu____819)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____823 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____824 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____823, uu____824)
              in
           match uu____810 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___113_833  ->
            match uu___113_833 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____840 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____843),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___114_866  ->
           match uu___114_866 with
           | UNIV uu____868 -> None
           | TERM ((u,uu____872),t) ->
               let uu____876 = FStar_Unionfind.equivalent uv u  in
               if uu____876 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___115_895  ->
           match uu___115_895 with
           | UNIV (u',t) ->
               let uu____899 = FStar_Unionfind.equivalent u u'  in
               if uu____899 then Some t else None
           | uu____903 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____910 =
        let uu____911 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____911
         in
      FStar_Syntax_Subst.compress uu____910
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____918 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____918
  
let norm_arg env t =
  let uu____937 = sn env (Prims.fst t)  in (uu____937, (Prims.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____954  ->
              match uu____954 with
              | (x,imp) ->
                  let uu____961 =
                    let uu___133_962 = x  in
                    let uu____963 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___133_962.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___133_962.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____963
                    }  in
                  (uu____961, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____978 = aux u3  in FStar_Syntax_Syntax.U_succ uu____978
        | FStar_Syntax_Syntax.U_max us ->
            let uu____981 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____981
        | uu____983 -> u2  in
      let uu____984 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____984
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1091 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1091 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1103;
               FStar_Syntax_Syntax.pos = uu____1104;
               FStar_Syntax_Syntax.vars = uu____1105;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1126 =
                 let uu____1127 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1128 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1127
                   uu____1128
                  in
               failwith uu____1126)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1163 =
             let uu____1164 = FStar_Syntax_Subst.compress t1'  in
             uu____1164.FStar_Syntax_Syntax.n  in
           match uu____1163 with
           | FStar_Syntax_Syntax.Tm_refine uu____1176 -> aux true t1'
           | uu____1181 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _
       |FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_arrow _
          |FStar_Syntax_Syntax.Tm_abs _
           |FStar_Syntax_Syntax.Tm_uvar _
            |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
        -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta _
      |FStar_Syntax_Syntax.Tm_ascribed _
       |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1216 =
          let uu____1217 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1218 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1217
            uu____1218
           in
        failwith uu____1216
     in
  let uu____1228 = whnf env t1  in aux false uu____1228 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1237 =
        let uu____1247 = empty_worklist env  in
        base_and_refinement env uu____1247 t  in
      FStar_All.pipe_right uu____1237 Prims.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1271 = FStar_Syntax_Syntax.null_bv t  in
    (uu____1271, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____1291 = base_and_refinement env wl t  in
  match uu____1291 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____1350 =
  match uu____1350 with
  | (t_base,refopt) ->
      let uu____1364 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____1364 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___116_1388  ->
      match uu___116_1388 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1392 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1393 =
            let uu____1394 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____1394  in
          let uu____1395 =
            let uu____1396 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____1396  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1392 uu____1393
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1395
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1400 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1401 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1402 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1400 uu____1401
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1402
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____1406 =
      let uu____1408 =
        let uu____1410 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1420  ->
                  match uu____1420 with | (uu____1424,uu____1425,x) -> x))
           in
        FStar_List.append wl.attempting uu____1410  in
      FStar_List.map (wl_prob_to_string wl) uu____1408  in
    FStar_All.pipe_right uu____1406 (FStar_String.concat "\n\t")
  
let mk_abs :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun ys  ->
      fun t  ->
        fun c  ->
          let uu____1446 =
            let uu____1453 =
              let uu____1459 = FStar_TypeChecker_Env.lcomp_of_comp env c  in
              FStar_Util.Inl uu____1459  in
            Some uu____1453  in
          FStar_Syntax_Util.abs ys t uu____1446
  
let u_abs :
  worklist ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun wl  ->
    fun k  ->
      fun ys  ->
        fun t  ->
          let uu____1486 =
            let uu____1496 =
              let uu____1497 = FStar_Syntax_Subst.compress k  in
              uu____1497.FStar_Syntax_Syntax.n  in
            match uu____1496 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                if (FStar_List.length bs) = (FStar_List.length ys)
                then
                  let uu____1538 = FStar_Syntax_Subst.open_comp bs c  in
                  ((ys, t), uu____1538)
                else
                  (let uu____1552 = FStar_Syntax_Util.abs_formals t  in
                   match uu____1552 with
                   | (ys',t1,uu____1573) ->
                       let uu____1586 =
                         FStar_Syntax_Util.arrow_formals_comp k  in
                       (((FStar_List.append ys ys'), t1), uu____1586))
            | uu____1607 ->
                let uu____1608 =
                  let uu____1614 = FStar_Syntax_Syntax.mk_Total k  in
                  ([], uu____1614)  in
                ((ys, t), uu____1608)
             in
          match uu____1486 with
          | ((ys1,t1),(xs,c)) ->
              if (FStar_List.length xs) <> (FStar_List.length ys1)
              then
                FStar_Syntax_Util.abs ys1 t1
                  (Some
                     (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
              else
                (let c1 =
                   let uu____1669 = FStar_Syntax_Util.rename_binders xs ys1
                      in
                   FStar_Syntax_Subst.subst_comp uu____1669 c  in
                 mk_abs wl.tcenv ys1 t1 c1)
  
let solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term Prims.option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | None  -> FStar_Syntax_Util.t_true
              | Some phi -> phi  in
            let uu____1692 = p_guard prob  in
            match uu____1692 with
            | (uu____1695,uv) ->
                ((let uu____1698 =
                    let uu____1699 = FStar_Syntax_Subst.compress uv  in
                    uu____1699.FStar_Syntax_Syntax.n  in
                  match uu____1698 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs wl k bs phi  in
                      ((let uu____1719 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____1719
                        then
                          let uu____1720 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____1721 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____1722 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____1720
                            uu____1721 uu____1722
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____1726 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___134_1729 = wl  in
                  {
                    attempting = (uu___134_1729.attempting);
                    wl_deferred = (uu___134_1729.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___134_1729.defer_ok);
                    smt_ok = (uu___134_1729.smt_ok);
                    tcenv = (uu___134_1729.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____1742 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____1742
         then
           let uu____1743 = FStar_Util.string_of_int pid  in
           let uu____1744 =
             let uu____1745 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____1745 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____1743 uu____1744
         else ());
        commit sol;
        (let uu___135_1750 = wl  in
         {
           attempting = (uu___135_1750.attempting);
           wl_deferred = (uu___135_1750.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___135_1750.defer_ok);
           smt_ok = (uu___135_1750.smt_ok);
           tcenv = (uu___135_1750.tcenv)
         })
  
let solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term Prims.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard t g =
            match (t, g) with
            | (uu____1779,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____1787 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____1787
             in
          (let uu____1793 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____1793
           then
             let uu____1794 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____1795 =
               let uu____1796 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____1796 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____1794 uu____1795
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____1821 =
    let uu____1825 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____1825 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____1821
    (FStar_Util.for_some
       (fun uu____1846  ->
          match uu____1846 with
          | (uv,uu____1854) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____1898 = occurs wl uk t  in Prims.op_Negation uu____1898  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____1903 =
         let uu____1904 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk)
            in
         let uu____1908 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____1904 uu____1908
          in
       Some uu____1903)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____1956 = occurs_check env wl uk t  in
  match uu____1956 with
  | (occurs_ok,msg) ->
      let uu____1973 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____1973, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set v1  in
  let uu____2037 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2061  ->
            fun uu____2062  ->
              match (uu____2061, uu____2062) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2105 =
                    let uu____2106 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2106  in
                  if uu____2105
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2120 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2120
                     then
                       let uu____2127 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2127)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2037 with | (isect,uu____2149) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2198  ->
          fun uu____2199  ->
            match (uu____2198, uu____2199) with
            | ((a,uu____2209),(b,uu____2211)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2255 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2261  ->
                match uu____2261 with
                | (b,uu____2265) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2255 then None else Some (a, (Prims.snd hd1))
  | uu____2274 -> None 
let rec pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders Prims.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____2317 = pat_var_opt env seen hd1  in
            (match uu____2317 with
             | None  ->
                 ((let uu____2325 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____2325
                   then
                     let uu____2326 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2326
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2338 =
      let uu____2339 = FStar_Syntax_Subst.compress t  in
      uu____2339.FStar_Syntax_Syntax.n  in
    match uu____2338 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2355 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2417;
         FStar_Syntax_Syntax.pos = uu____2418;
         FStar_Syntax_Syntax.vars = uu____2419;_},args)
      -> (t, uv, k, args)
  | uu____2460 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____2514 = destruct_flex_t t  in
  match uu____2514 with
  | (t1,uv,k,args) ->
      let uu____2582 = pat_vars env [] args  in
      (match uu____2582 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____2638 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option *
  FStar_Syntax_Syntax.delta_depth Prims.option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____2686 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option *
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____2709 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____2713 -> false
  
let head_match : match_result -> match_result =
  fun uu___117_2716  ->
    match uu___117_2716 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____2725 -> HeadMatch
  
let fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth
  =
  fun env  ->
    fun fv  ->
      match fv.FStar_Syntax_Syntax.fv_delta with
      | FStar_Syntax_Syntax.Delta_abstract d ->
          if
            (env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
              ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr
          then d
          else FStar_Syntax_Syntax.Delta_constant
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth Prims.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta _|FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_name _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
          -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t2,_,_)
         |FStar_Syntax_Syntax.Tm_app (t2,_)|FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
             FStar_Syntax_Syntax.sort = t2;_},_)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_arrow _|FStar_Syntax_Syntax.Tm_abs _ ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv -> Some (fv_delta_depth env fv)
  
let rec head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____2815 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____2815
            then FullMatch
            else
              MisMatch
                ((Some (fv_delta_depth env f)),
                  (Some (fv_delta_depth env g)))
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____2820),FStar_Syntax_Syntax.Tm_uinst (g,uu____2822)) ->
            let uu____2831 = head_matches env f g  in
            FStar_All.pipe_right uu____2831 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____2838),FStar_Syntax_Syntax.Tm_uvar (uv',uu____2840)) ->
            let uu____2865 = FStar_Unionfind.equivalent uv uv'  in
            if uu____2865 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____2873),FStar_Syntax_Syntax.Tm_refine (y,uu____2875)) ->
            let uu____2884 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____2884 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____2886),uu____2887) ->
            let uu____2892 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____2892 head_match
        | (uu____2893,FStar_Syntax_Syntax.Tm_refine (x,uu____2895)) ->
            let uu____2900 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____2900 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____2906),FStar_Syntax_Syntax.Tm_app (head',uu____2908))
            ->
            let uu____2937 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____2937 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____2939),uu____2940) ->
            let uu____2955 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____2955 head_match
        | (uu____2956,FStar_Syntax_Syntax.Tm_app (head1,uu____2958)) ->
            let uu____2973 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____2973 head_match
        | uu____2974 ->
            let uu____2977 =
              let uu____2982 = delta_depth_of_term env t11  in
              let uu____2984 = delta_depth_of_term env t21  in
              (uu____2982, uu____2984)  in
            MisMatch uu____2977
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3020 = FStar_Syntax_Util.head_and_args t  in
    match uu____3020 with
    | (head1,uu____3032) ->
        let uu____3047 =
          let uu____3048 = FStar_Syntax_Util.un_uinst head1  in
          uu____3048.FStar_Syntax_Syntax.n  in
        (match uu____3047 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3053 =
               let uu____3054 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3054 FStar_Option.isSome  in
             if uu____3053
             then
               let uu____3068 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3068 (fun _0_32  -> Some _0_32)
             else None
         | uu____3071 -> None)
     in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None))  in
  let fail r = (r, None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),_)|MisMatch
      (_,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3151 =
             let uu____3156 = maybe_inline t11  in
             let uu____3158 = maybe_inline t21  in (uu____3156, uu____3158)
              in
           match uu____3151 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3183 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____3183 with
         | None  -> fail r
         | Some d ->
             let t12 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t11
                in
             let t22 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
        let uu____3198 =
          if d1_greater_than_d2
          then
            let t1' =
              normalize_refinement
                [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                FStar_TypeChecker_Normalize.WHNF] env wl t11
               in
            (t1', t21)
          else
            (let t2' =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             let uu____3206 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____3206))
           in
        (match uu____3198 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3214 -> fail r
    | uu____3219 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3244 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3274 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders ->
    FStar_Range.range -> FStar_Syntax_Syntax.term
  =
  fun binders  ->
    fun r  ->
      let uu____3289 = FStar_Syntax_Util.type_u ()  in
      match uu____3289 with
      | (t,uu____3293) ->
          let uu____3294 = FStar_TypeChecker_Env.new_uvar r binders t  in
          Prims.fst uu____3294
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3303 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____3303 Prims.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term) *
        (FStar_Syntax_Syntax.term -> Prims.bool) *
        (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____3345 = head_matches env t1 t'  in
        match uu____3345 with
        | MisMatch uu____3346 -> false
        | uu____3351 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3411,imp),T (t2,uu____3414)) -> (t2, imp)
                     | uu____3431 -> failwith "Bad reconstruction") args
                args'
               in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3475  ->
                    match uu____3475 with
                    | (t2,uu____3483) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3516 = failwith "Bad reconstruction"  in
          let uu____3517 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3517 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3564))::tcs2) ->
                       aux
                         (((let uu___136_3586 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___136_3586.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___136_3586.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____3596 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___118_3625 =
                 match uu___118_3625 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____3688 = decompose1 [] bs1  in
               (rebuild, matches, uu____3688))
      | uu____3714 ->
          let rebuild uu___119_3719 =
            match uu___119_3719 with
            | [] -> t1
            | uu____3721 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___120_3740  ->
    match uu___120_3740 with
    | T (t,uu____3742) -> t
    | uu____3751 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___121_3754  ->
    match uu___121_3754 with
    | T (t,uu____3756) -> FStar_Syntax_Syntax.as_arg t
    | uu____3765 -> failwith "Impossible"
  
let imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder Prims.option * variance * tc)
            Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list * tc Prims.list *
              FStar_Syntax_Syntax.formula)
  =
  fun orig  ->
    fun env  ->
      fun scope  ->
        fun ps  ->
          fun qs  ->
            let r = p_loc orig  in
            let rel = p_rel orig  in
            let sub_prob scope1 args q =
              match q with
              | (uu____3839,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____3858 = FStar_TypeChecker_Env.new_uvar r scope1 k
                     in
                  (match uu____3858 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____3870 ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_app (gi, args))) None
                               r
                          in
                       let uu____3889 =
                         let uu____3890 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_33  ->
                              FStar_TypeChecker_Common.TProb _0_33)
                           uu____3890
                          in
                       ((T (gi_xs, mk_kind)), uu____3889))
              | (uu____3899,uu____3900,C uu____3901) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____3988 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____3999;
                         FStar_Syntax_Syntax.pos = uu____4000;
                         FStar_Syntax_Syntax.vars = uu____4001;_})
                        ->
                        let uu____4016 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4016 with
                         | (T (gi_xs,uu____4032),prob) ->
                             let uu____4042 =
                               let uu____4043 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_34  -> C _0_34)
                                 uu____4043
                                in
                             (uu____4042, [prob])
                         | uu____4045 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4055;
                         FStar_Syntax_Syntax.pos = uu____4056;
                         FStar_Syntax_Syntax.vars = uu____4057;_})
                        ->
                        let uu____4072 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4072 with
                         | (T (gi_xs,uu____4088),prob) ->
                             let uu____4098 =
                               let uu____4099 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_35  -> C _0_35)
                                 uu____4099
                                in
                             (uu____4098, [prob])
                         | uu____4101 -> failwith "impossible")
                    | (uu____4107,uu____4108,C comp) ->
                        let nct =
                          FStar_TypeChecker_Env.comp_as_normal_comp_typ env
                            comp
                           in
                        let components =
                          [(None, COVARIANT,
                             (T
                                ((Prims.fst
                                    nct.FStar_TypeChecker_Env.nct_result),
                                  kind_type)));
                          (None, INVARIANT,
                            (T
                               ((Prims.fst nct.FStar_TypeChecker_Env.nct_wp),
                                 generic_kind)))]
                           in
                        let components1 =
                          FStar_List.fold_right
                            (fun t  ->
                               fun out  ->
                                 (None, INVARIANT,
                                   (T ((Prims.fst t), generic_kind)))
                                 :: out)
                            nct.FStar_TypeChecker_Env.nct_indices components
                           in
                        let uu____4212 =
                          let uu____4217 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____4217 FStar_List.unzip
                           in
                        (match uu____4212 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4246 =
                                 let uu____4247 =
                                   FStar_All.pipe_right tcs
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_typ_name =
                                     (nct.FStar_TypeChecker_Env.nct_name);
                                   FStar_Syntax_Syntax.comp_univs =
                                     (nct.FStar_TypeChecker_Env.nct_univs);
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4247;
                                   FStar_Syntax_Syntax.flags =
                                     (nct.FStar_TypeChecker_Env.nct_flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4246
                                in
                             ((C gi_xs), sub_probs))
                    | uu____4256 ->
                        let uu____4263 = sub_prob scope1 args q  in
                        (match uu____4263 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____3988 with
                   | (tc,probs) ->
                       let uu____4281 =
                         match q with
                         | (Some b,uu____4307,uu____4308) ->
                             let uu____4316 =
                               let uu____4320 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____4320 :: args  in
                             ((Some b), (b :: scope1), uu____4316)
                         | uu____4338 -> (None, scope1, args)  in
                       (match uu____4281 with
                        | (bopt,scope2,args1) ->
                            let uu____4381 = aux scope2 args1 qs2  in
                            (match uu____4381 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____4402 =
                                         let uu____4404 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst))
                                            in
                                         f :: uu____4404  in
                                       FStar_Syntax_Util.mk_conj_l uu____4402
                                   | Some b ->
                                       let uu____4416 =
                                         let uu____4418 =
                                           FStar_Syntax_Util.mk_forall
                                             (Prims.fst b) f
                                            in
                                         let uu____4419 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob) Prims.fst))
                                            in
                                         uu____4418 :: uu____4419  in
                                       FStar_Syntax_Util.mk_conj_l uu____4416
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
            aux scope ps qs
  
type flex_t =
  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar *
    FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
    FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) *
    FStar_Syntax_Syntax.arg Prims.list *
    ((tc Prims.list -> FStar_Syntax_Syntax.typ) *
    (FStar_Syntax_Syntax.typ -> Prims.bool) * (FStar_Syntax_Syntax.binder
    Prims.option * variance * tc) Prims.list))
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___137_4472 = p  in
  let uu____4475 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____4476 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___137_4472.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4475;
    FStar_TypeChecker_Common.relation =
      (uu___137_4472.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4476;
    FStar_TypeChecker_Common.element =
      (uu___137_4472.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___137_4472.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___137_4472.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___137_4472.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___137_4472.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___137_4472.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4486 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____4486
            (fun _0_36  -> FStar_TypeChecker_Common.TProb _0_36)
      | FStar_TypeChecker_Common.CProb uu____4491 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4505 = compress_prob wl pr  in
        FStar_All.pipe_right uu____4505 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4511 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____4511 with
           | (lh,uu____4524) ->
               let uu____4539 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____4539 with
                | (rh,uu____4552) ->
                    let uu____4567 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4576,FStar_Syntax_Syntax.Tm_uvar uu____4577)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4602,uu____4603)
                          ->
                          let uu____4612 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____4612 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____4652 ->
                                    let rank =
                                      let uu____4659 = is_top_level_prob prob
                                         in
                                      if uu____4659
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____4661 =
                                      let uu___138_4664 = tp  in
                                      let uu____4667 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___138_4664.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___138_4664.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___138_4664.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____4667;
                                        FStar_TypeChecker_Common.element =
                                          (uu___138_4664.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___138_4664.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___138_4664.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___138_4664.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___138_4664.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___138_4664.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____4661)))
                      | (uu____4677,FStar_Syntax_Syntax.Tm_uvar uu____4678)
                          ->
                          let uu____4687 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____4687 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____4727 ->
                                    let uu____4733 =
                                      let uu___139_4738 = tp  in
                                      let uu____4741 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___139_4738.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____4741;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___139_4738.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___139_4738.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___139_4738.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___139_4738.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___139_4738.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___139_4738.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___139_4738.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___139_4738.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____4733)))
                      | (uu____4757,uu____4758) -> (rigid_rigid, tp)  in
                    (match uu____4567 with
                     | (rank,tp1) ->
                         let uu____4769 =
                           FStar_All.pipe_right
                             (let uu___140_4772 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___140_4772.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___140_4772.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___140_4772.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___140_4772.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___140_4772.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___140_4772.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___140_4772.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___140_4772.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___140_4772.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_37  ->
                                FStar_TypeChecker_Common.TProb _0_37)
                            in
                         (rank, uu____4769))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____4778 =
            FStar_All.pipe_right
              (let uu___141_4781 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___141_4781.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___141_4781.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___141_4781.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___141_4781.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___141_4781.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___141_4781.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___141_4781.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___141_4781.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___141_4781.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_38  -> FStar_TypeChecker_Common.CProb _0_38)
             in
          (rigid_rigid, uu____4778)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option *
      FStar_TypeChecker_Common.prob Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____4813 probs =
      match uu____4813 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____4843 = rank wl hd1  in
               (match uu____4843 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | None  ->
                           ((Some hd2), (FStar_List.append out tl1), rank1)
                       | Some m ->
                           ((Some hd2), (FStar_List.append out (m :: tl1)),
                             rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | None  -> aux (rank1, (Some hd2), out) tl1
                         | Some m -> aux (rank1, (Some hd2), (m :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux ((flex_flex + (Prims.parse_int "1")), None, []) wl.attempting
  
let is_flex_rigid : Prims.int -> Prims.bool =
  fun rank1  -> (flex_refine_inner <= rank1) && (rank1 <= flex_rigid) 
let is_rigid_flex : Prims.int -> Prims.bool =
  fun rank1  -> (rigid_flex <= rank1) && (rank1 <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let uu___is_UDeferred : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____4908 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____4920 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____4932 -> false
  
let __proj__UFailed__item___0 : univ_eq_sol -> Prims.string =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let rec really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
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
                        let uu____4969 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____4969 with
                        | (k,uu____4973) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____4978 -> false)))
            | uu____4979 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let try_umax_components u12 u22 msg =
            match (u12, u22) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl1 us11 us21 =
                    match (us11, us21) with
                    | (u13::us12,u23::us22) ->
                        let uu____5022 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5022 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5025 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5031 =
                     let uu____5032 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5033 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5032
                       uu____5033
                      in
                   UFailed uu____5031)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5050 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5050 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5053 ->
                let uu____5056 =
                  let uu____5057 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____5058 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5057
                    uu____5058 msg
                   in
                UFailed uu____5056
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5065 =
                let uu____5066 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5067 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5066 uu____5067
                 in
              failwith uu____5065
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5079 = FStar_Unionfind.equivalent v1 v2  in
              if uu____5079
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____5092 = occurs_univ v1 u3  in
              if uu____5092
              then
                let uu____5093 =
                  let uu____5094 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____5095 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5094 uu____5095
                   in
                try_umax_components u11 u21 uu____5093
              else
                (let uu____5097 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____5097)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____5107 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____5107
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_zero )
            |(FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_name _)
             |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ _)
              |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name _)
               |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ _)
                |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_zero )
              -> UFailed "Incompatible universes"
  
let solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders bc1 bc2 =
  let uu____5178 = bc1  in
  match uu____5178 with
  | (bs1,mk_cod1) ->
      let uu____5203 = bc2  in
      (match uu____5203 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5250 = FStar_Util.first_N n1 bs  in
             match uu____5250 with
             | (bs3,rest) ->
                 let uu____5264 = mk_cod rest  in (bs3, uu____5264)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____5282 =
               let uu____5286 = mk_cod1 []  in (bs1, uu____5286)  in
             let uu____5288 =
               let uu____5292 = mk_cod2 []  in (bs2, uu____5292)  in
             (uu____5282, uu____5288)
           else
             if l1 > l2
             then
               (let uu____5314 = curry l2 bs1 mk_cod1  in
                let uu____5321 =
                  let uu____5325 = mk_cod2 []  in (bs2, uu____5325)  in
                (uu____5314, uu____5321))
             else
               (let uu____5334 =
                  let uu____5338 = mk_cod1 []  in (bs1, uu____5338)  in
                let uu____5340 = curry l1 bs2 mk_cod2  in
                (uu____5334, uu____5340)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5444 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____5444
       then
         let uu____5445 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5445
       else ());
      (let uu____5447 = next_prob probs  in
       match uu____5447 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___142_5460 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___142_5460.wl_deferred);
               ctr = (uu___142_5460.ctr);
               defer_ok = (uu___142_5460.defer_ok);
               smt_ok = (uu___142_5460.smt_ok);
               tcenv = (uu___142_5460.tcenv)
             }  in
           (match hd1 with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs1.defer_ok) &&
                     (flex_refine_inner <= rank1))
                    && (rank1 <= flex_rigid)
                then
                  let uu____5467 = solve_flex_rigid_join env tp probs1  in
                  (match uu____5467 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5471 = solve_rigid_flex_meet env tp probs1  in
                     match uu____5471 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5475,uu____5476) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5485 ->
                let uu____5490 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5518  ->
                          match uu____5518 with
                          | (c,uu____5523,uu____5524) -> c < probs.ctr))
                   in
                (match uu____5490 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5546 =
                            FStar_List.map
                              (fun uu____5552  ->
                                 match uu____5552 with
                                 | (uu____5558,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____5546
                      | uu____5561 ->
                          let uu____5566 =
                            let uu___143_5567 = probs  in
                            let uu____5568 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5577  ->
                                      match uu____5577 with
                                      | (uu____5581,uu____5582,y) -> y))
                               in
                            {
                              attempting = uu____5568;
                              wl_deferred = rest;
                              ctr = (uu___143_5567.ctr);
                              defer_ok = (uu___143_5567.defer_ok);
                              smt_ok = (uu___143_5567.smt_ok);
                              tcenv = (uu___143_5567.tcenv)
                            }  in
                          solve env uu____5566))))

and solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____5589 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____5589 with
            | USolved wl1 ->
                let uu____5591 = solve_prob orig None [] wl1  in
                solve env uu____5591
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 -> solve env (defer "" orig wl1)

and solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol
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
                  let uu____5625 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____5625 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____5628 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____5636;
                  FStar_Syntax_Syntax.pos = uu____5637;
                  FStar_Syntax_Syntax.vars = uu____5638;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____5641;
                  FStar_Syntax_Syntax.pos = uu____5642;
                  FStar_Syntax_Syntax.vars = uu____5643;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____5659 -> USolved wl

and giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____5667 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____5667
              then
                let uu____5668 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____5668 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____5676 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____5676
         then
           let uu____5677 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____5677
         else ());
        (let uu____5679 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____5679 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____5721 = head_matches_delta env () t1 t2  in
               match uu____5721 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____5743 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____5769 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____5778 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____5779 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____5778, uu____5779)
                          | None  ->
                              let uu____5782 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____5783 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____5782, uu____5783)
                           in
                        (match uu____5769 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____5805 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_39  ->
                                    FStar_TypeChecker_Common.TProb _0_39)
                                 uu____5805
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____5828 =
                                    let uu____5834 =
                                      let uu____5837 =
                                        let uu____5840 =
                                          let uu____5841 =
                                            let uu____5846 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____5846)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____5841
                                           in
                                        FStar_Syntax_Syntax.mk uu____5840  in
                                      uu____5837 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5859 =
                                      let uu____5861 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____5861]  in
                                    (uu____5834, uu____5859)  in
                                  Some uu____5828
                              | (uu____5870,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5872)) ->
                                  let uu____5877 =
                                    let uu____5881 =
                                      let uu____5883 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____5883]  in
                                    (t11, uu____5881)  in
                                  Some uu____5877
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5889),uu____5890) ->
                                  let uu____5895 =
                                    let uu____5899 =
                                      let uu____5901 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____5901]  in
                                    (t21, uu____5899)  in
                                  Some uu____5895
                              | uu____5906 ->
                                  let uu____5909 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____5909 with
                                   | (head1,uu____5924) ->
                                       let uu____5939 =
                                         let uu____5940 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____5940.FStar_Syntax_Syntax.n  in
                                       (match uu____5939 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____5947;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____5949;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant
                                               in
                                            let t12 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t11
                                               in
                                            let t22 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t21
                                               in
                                            disjoin t12 t22
                                        | uu____5958 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5967) ->
                  let uu____5980 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___122_5989  ->
                            match uu___122_5989 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____5994 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____5994 with
                                      | (u',uu____6005) ->
                                          let uu____6020 =
                                            let uu____6021 = whnf env u'  in
                                            uu____6021.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6020 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6025) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6041 -> false))
                                 | uu____6042 -> false)
                            | uu____6044 -> false))
                     in
                  (match uu____5980 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6065 tps =
                         match uu____6065 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6092 =
                                    let uu____6097 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____6097  in
                                  (match uu____6092 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6116 -> None)
                          in
                       let uu____6121 =
                         let uu____6126 =
                           let uu____6130 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____6130, [])  in
                         make_lower_bound uu____6126 lower_bounds  in
                       (match uu____6121 with
                        | None  ->
                            ((let uu____6137 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6137
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             None)
                        | Some (lhs_bound,sub_probs) ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____6150 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6150
                              then
                                let wl' =
                                  let uu___144_6152 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___144_6152.wl_deferred);
                                    ctr = (uu___144_6152.ctr);
                                    defer_ok = (uu___144_6152.defer_ok);
                                    smt_ok = (uu___144_6152.smt_ok);
                                    tcenv = (uu___144_6152.tcenv)
                                  }  in
                                let uu____6153 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6153
                              else ());
                             (let uu____6155 =
                                solve_t env eq_prob
                                  (let uu___145_6156 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___145_6156.wl_deferred);
                                     ctr = (uu___145_6156.ctr);
                                     defer_ok = (uu___145_6156.defer_ok);
                                     smt_ok = (uu___145_6156.smt_ok);
                                     tcenv = (uu___145_6156.tcenv)
                                   })
                                 in
                              match uu____6155 with
                              | Success uu____6158 ->
                                  let wl1 =
                                    let uu___146_6160 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___146_6160.wl_deferred);
                                      ctr = (uu___146_6160.ctr);
                                      defer_ok = (uu___146_6160.defer_ok);
                                      smt_ok = (uu___146_6160.smt_ok);
                                      tcenv = (uu___146_6160.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____6162 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____6165 -> None))))
              | uu____6166 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6173 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6173
         then
           let uu____6174 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6174
         else ());
        (let uu____6176 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____6176 with
         | (u,args) ->
             let uu____6203 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____6203 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____6234 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____6234 with
                    | (h1,args1) ->
                        let uu____6262 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____6262 with
                         | (h2,uu____6275) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6294 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____6294
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6307 =
                                          let uu____6309 =
                                            let uu____6310 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_40  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_40) uu____6310
                                             in
                                          [uu____6309]  in
                                        Some uu____6307))
                                  else None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6332 =
                                          let uu____6334 =
                                            let uu____6335 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_41  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_41) uu____6335
                                             in
                                          [uu____6334]  in
                                        Some uu____6332))
                                  else None
                              | uu____6343 -> None))
                     in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort
                           in
                        (match m with
                         | None  -> None
                         | Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____6409 =
                               let uu____6415 =
                                 let uu____6418 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____6418  in
                               (uu____6415, m1)  in
                             Some uu____6409)
                    | (uu____6427,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6429)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6461),uu____6462) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6493 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6527) ->
                       let uu____6540 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___123_6549  ->
                                 match uu___123_6549 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6554 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____6554 with
                                           | (u',uu____6565) ->
                                               let uu____6580 =
                                                 let uu____6581 = whnf env u'
                                                    in
                                                 uu____6581.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6580 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6585) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6601 -> false))
                                      | uu____6602 -> false)
                                 | uu____6604 -> false))
                          in
                       (match uu____6540 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____6629 tps =
                              match uu____6629 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____6670 =
                                         let uu____6677 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____6677  in
                                       (match uu____6670 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____6712 -> None)
                               in
                            let uu____6719 =
                              let uu____6726 =
                                let uu____6732 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____6732, [])  in
                              make_upper_bound uu____6726 upper_bounds  in
                            (match uu____6719 with
                             | None  ->
                                 ((let uu____6741 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____6741
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  None)
                             | Some (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     None tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____6760 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____6760
                                   then
                                     let wl' =
                                       let uu___147_6762 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___147_6762.wl_deferred);
                                         ctr = (uu___147_6762.ctr);
                                         defer_ok = (uu___147_6762.defer_ok);
                                         smt_ok = (uu___147_6762.smt_ok);
                                         tcenv = (uu___147_6762.tcenv)
                                       }  in
                                     let uu____6763 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____6763
                                   else ());
                                  (let uu____6765 =
                                     solve_t env eq_prob
                                       (let uu___148_6766 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___148_6766.wl_deferred);
                                          ctr = (uu___148_6766.ctr);
                                          defer_ok = (uu___148_6766.defer_ok);
                                          smt_ok = (uu___148_6766.smt_ok);
                                          tcenv = (uu___148_6766.tcenv)
                                        })
                                      in
                                   match uu____6765 with
                                   | Success uu____6768 ->
                                       let wl1 =
                                         let uu___149_6770 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___149_6770.wl_deferred);
                                           ctr = (uu___149_6770.ctr);
                                           defer_ok =
                                             (uu___149_6770.defer_ok);
                                           smt_ok = (uu___149_6770.smt_ok);
                                           tcenv = (uu___149_6770.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____6772 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____6775 -> None))))
                   | uu____6776 -> failwith "Impossible: Not a flex-rigid")))

and solve_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders ->
        FStar_TypeChecker_Common.prob ->
          worklist ->
            (FStar_Syntax_Syntax.binders ->
               FStar_TypeChecker_Env.env ->
                 FStar_Syntax_Syntax.subst_elt Prims.list ->
                   FStar_TypeChecker_Common.prob)
              -> solution
  =
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              let rec aux scope env1 subst1 xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs (FStar_List.rev scope) env1 subst1  in
                    ((let uu____6841 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____6841
                      then
                        let uu____6842 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____6842
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst  in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___150_6874 = hd1  in
                      let uu____6875 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___150_6874.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___150_6874.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____6875
                      }  in
                    let hd21 =
                      let uu___151_6879 = hd2  in
                      let uu____6880 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___151_6879.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___151_6879.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____6880
                      }  in
                    let prob =
                      let uu____6884 =
                        let uu____6887 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____6887 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
                        uu____6884
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____6895 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____6895
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____6898 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____6898 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____6916 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst
                              in
                           let uu____6919 =
                             FStar_Syntax_Util.close_forall [(hd12, imp)] phi
                              in
                           FStar_Syntax_Util.mk_conj uu____6916 uu____6919
                            in
                         ((let uu____6925 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____6925
                           then
                             let uu____6926 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____6927 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____6926 uu____6927
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____6942 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____6948 = aux scope env [] bs1 bs2  in
              match uu____6948 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____6964 = compress_tprob wl problem  in
        solve_t' env uu____6964 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____6997 = head_matches_delta env1 wl1 t1 t2  in
          match uu____6997 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7014,uu____7015) ->
                   let may_relate head3 =
                     match head3.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7037 -> false  in
                   if
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                   then
                     let guard =
                       if
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                       then mk_eq2 env1 t1 t2
                       else
                         (let has_type_guard t11 t21 =
                            match problem.FStar_TypeChecker_Common.element
                            with
                            | Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | None  ->
                                let x = FStar_Syntax_Syntax.new_bv None t11
                                   in
                                let uu____7053 =
                                  let uu____7054 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7054 t21
                                   in
                                FStar_Syntax_Util.mk_forall x uu____7053
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____7056 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____7056
                   else giveup env1 "head mismatch" orig
               | (uu____7058,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___152_7066 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___152_7066.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___152_7066.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___152_7066.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___152_7066.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___152_7066.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___152_7066.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___152_7066.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___152_7066.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7067,None ) ->
                   ((let uu____7074 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7074
                     then
                       let uu____7075 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7076 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____7077 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____7078 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7075
                         uu____7076 uu____7077 uu____7078
                     else ());
                    (let uu____7080 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____7080 with
                     | (head11,args1) ->
                         let uu____7106 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____7106 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7146 =
                                  let uu____7147 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____7148 = args_to_string args1  in
                                  let uu____7149 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____7150 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7147 uu____7148 uu____7149
                                    uu____7150
                                   in
                                giveup env1 uu____7146 orig
                              else
                                (let uu____7152 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7155 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____7155 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____7152
                                 then
                                   let uu____7156 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____7156 with
                                   | USolved wl2 ->
                                       let uu____7158 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____7158
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7162 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____7162 with
                                    | (base1,refinement1) ->
                                        let uu____7188 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____7188 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7242 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____7242 with
                                                   | UFailed msg ->
                                                       giveup env1 msg orig
                                                   | UDeferred wl2 ->
                                                       solve env1
                                                         (defer
                                                            "universe constraints"
                                                            orig wl2)
                                                   | USolved wl2 ->
                                                       let subprobs =
                                                         FStar_List.map2
                                                           (fun uu____7252 
                                                              ->
                                                              fun uu____7253 
                                                                ->
                                                                match 
                                                                  (uu____7252,
                                                                    uu____7253)
                                                                with
                                                                | ((a,uu____7263),
                                                                   (a',uu____7265))
                                                                    ->
                                                                    let uu____7270
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a' None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_43  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_43)
                                                                    uu____7270)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____7276 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7276
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7280 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___153_7313 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___153_7313.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____7333 = p  in
          match uu____7333 with
          | (((u,k),xs,c),ps,(h,uu____7344,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7393 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____7393 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7407 = h gs_xs  in
                     mk_abs env1 xs1 uu____7407 c  in
                   ((let uu____7409 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7409
                     then
                       let uu____7410 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____7411 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____7412 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____7413 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____7414 =
                         let uu____7415 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____7415
                           (FStar_String.concat ", ")
                          in
                       let uu____7418 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7410 uu____7411 uu____7412 uu____7413
                         uu____7414 uu____7418
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___124_7436 =
          match uu___124_7436 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____7465 = p  in
          match uu____7465 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7523 = FStar_List.nth ps i  in
              (match uu____7523 with
               | (pi,uu____7526) ->
                   let uu____7531 = FStar_List.nth xs i  in
                   (match uu____7531 with
                    | (xi,uu____7538) ->
                        let rec gs k =
                          let uu____7547 =
                            FStar_Syntax_Util.arrow_formals_comp k  in
                          match uu____7547 with
                          | (bs,uu____7558) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____7593)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____7601 =
                                      FStar_TypeChecker_Env.new_uvar r xs k_a
                                       in
                                    (match uu____7601 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs
                                            in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1  in
                                         let uu____7620 = aux subst2 tl1  in
                                         (match uu____7620 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____7635 =
                                                let uu____7637 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____7637 :: gi_xs'  in
                                              let uu____7638 =
                                                let uu____7640 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____7640 :: gi_ps'  in
                                              (uu____7635, uu____7638)))
                                 in
                              aux [] bs
                           in
                        let uu____7643 =
                          let uu____7644 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____7644
                           in
                        if uu____7643
                        then None
                        else
                          (let uu____7647 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____7647 with
                           | (g_xs,uu____7654) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____7661 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 mk_abs wl1.tcenv xs uu____7661 c  in
                               let sub1 =
                                 let uu____7667 =
                                   let uu____7670 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____7677 =
                                     let uu____7680 =
                                       FStar_List.map
                                         (fun uu____7686  ->
                                            match uu____7686 with
                                            | (uu____7691,uu____7692,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____7680  in
                                   mk_problem (p_scope orig) orig uu____7670
                                     (p_rel orig) uu____7677 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_44  ->
                                      FStar_TypeChecker_Common.TProb _0_44)
                                   uu____7667
                                  in
                               ((let uu____7702 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____7702
                                 then
                                   let uu____7703 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____7704 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____7703 uu____7704
                                 else ());
                                (let wl2 =
                                   let uu____7707 =
                                     let uu____7709 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1)
                                        in
                                     Some uu____7709  in
                                   solve_prob orig uu____7707
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____7714 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_45  -> Some _0_45) uu____7714)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____7738 = lhs  in
          match uu____7738 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____7761 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____7761 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____7783 =
                        let uu____7809 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____7809)  in
                      Some uu____7783
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____7892 =
                           let uu____7896 =
                             let uu____7897 = FStar_Syntax_Subst.compress k
                                in
                             uu____7897.FStar_Syntax_Syntax.n  in
                           (uu____7896, args)  in
                         match uu____7892 with
                         | (uu____7904,[]) ->
                             let uu____7906 =
                               let uu____7912 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____7912)  in
                             Some uu____7906
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____7929 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____7929 with
                              | (uv1,uv_args) ->
                                  let uu____7958 =
                                    let uu____7959 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____7959.FStar_Syntax_Syntax.n  in
                                  (match uu____7958 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____7966) ->
                                       let uu____7979 =
                                         pat_vars env [] uv_args  in
                                       (match uu____7979 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____7993  ->
                                                      let uu____7994 =
                                                        let uu____7995 =
                                                          let uu____7996 =
                                                            let uu____7999 =
                                                              let uu____8000
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8000
                                                                Prims.fst
                                                               in
                                                            FStar_TypeChecker_Env.new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____7999
                                                             in
                                                          Prims.fst
                                                            uu____7996
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____7995
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____7994))
                                               in
                                            let c1 =
                                              let uu____8006 =
                                                let uu____8007 =
                                                  let uu____8010 =
                                                    let uu____8011 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8011 Prims.fst
                                                     in
                                                  FStar_TypeChecker_Env.new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8010
                                                   in
                                                Prims.fst uu____8007  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8006
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____8018 =
                                                let uu____8019 =
                                                  let uu____8020 =
                                                    FStar_Syntax_Util.type_u
                                                      ()
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____8020 Prims.fst
                                                   in
                                                FStar_Syntax_Syntax.mk_Total
                                                  uu____8019
                                                 in
                                              mk_abs env scope k' uu____8018
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8033 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8038)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____8064 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____8064
                                 (fun _0_46  -> Some _0_46)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8083 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____8083 with
                                  | (args1,rest) ->
                                      let uu____8099 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____8099 with
                                       | (xs2,c2) ->
                                           let uu____8107 =
                                             let uu____8111 =
                                               FStar_TypeChecker_Env.result_typ
                                                 env c2
                                                in
                                             elim uu____8111 rest  in
                                           FStar_Util.bind_opt uu____8107
                                             (fun uu____8119  ->
                                                match uu____8119 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8141 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____8141 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8187 =
                                        let uu____8190 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8190
                                         in
                                      FStar_All.pipe_right uu____8187
                                        (fun _0_47  -> Some _0_47))
                         | uu____8198 ->
                             let uu____8202 =
                               let uu____8203 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____8207 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____8208 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8203 uu____8207 uu____8208
                                in
                             failwith uu____8202
                          in
                       let uu____8212 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____8212
                         (fun uu____8240  ->
                            match uu____8240 with
                            | (xs1,c1) ->
                                let uu____8268 =
                                  let uu____8291 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8291)
                                   in
                                Some uu____8268))
                 in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt  in
                   let tx = FStar_Unionfind.new_transaction ()  in
                   if i = (~- (Prims.parse_int "1"))
                   then
                     let uu____8363 = imitate orig env wl1 st  in
                     match uu____8363 with
                     | Failed uu____8368 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8374 = project orig env wl1 i st  in
                      match uu____8374 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____8392 = FStar_Syntax_Util.head_and_args t21  in
                match uu____8392 with
                | (hd1,uu____8403) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8421 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____8424 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____8424
                         then true
                         else
                           ((let uu____8427 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____8427
                             then
                               let uu____8428 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8428
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8436 =
                    let uu____8439 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____8439 Prims.fst  in
                  FStar_All.pipe_right uu____8436 FStar_Syntax_Free.names  in
                let uu____8470 = FStar_Util.set_is_empty fvs_hd  in
                if uu____8470
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____8479 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____8479 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8487 =
                            let uu____8488 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____8488
                             in
                          giveup_or_defer1 orig uu____8487
                        else
                          (let uu____8490 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____8490
                           then
                             let uu____8491 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____8491
                              then
                                let uu____8492 = subterms args_lhs  in
                                imitate' orig env wl1 uu____8492
                              else
                                ((let uu____8496 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____8496
                                  then
                                    let uu____8497 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____8498 = names_to_string fvs1  in
                                    let uu____8499 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____8497 uu____8498 uu____8499
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____8504 ->
                                        let uu____8505 = sn_binders env vars
                                           in
                                        u_abs wl1 k_uv uu____8505 t21
                                     in
                                  let wl2 =
                                    solve_prob orig None
                                      [TERM ((uv, k_uv), sol)] wl1
                                     in
                                  solve env wl2)))
                           else
                             if
                               ((Prims.op_Negation patterns_only) &&
                                  wl1.defer_ok)
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                             then
                               solve env
                                 (defer
                                    "flex pattern/rigid: occurs or freevar check"
                                    orig wl1)
                             else
                               (let uu____8514 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____8514
                                then
                                  ((let uu____8516 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____8516
                                    then
                                      let uu____8517 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____8518 = names_to_string fvs1
                                         in
                                      let uu____8519 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____8517 uu____8518 uu____8519
                                    else ());
                                   (let uu____8521 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____8521
                                      (~- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____8532 =
                        let uu____8533 = FStar_Syntax_Free.names t1  in
                        check_head uu____8533 t2  in
                      if uu____8532
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____8537 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____8537
                          then
                            let uu____8538 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____8538
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____8541 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____8541 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____8583 =
               match uu____8583 with
               | (t,u,k,args) ->
                   let uu____8613 = FStar_Syntax_Util.arrow_formals_comp k
                      in
                   (match uu____8613 with
                    | (all_formals,uu____8622) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____8710  ->
                                        match uu____8710 with
                                        | (x,imp) ->
                                            let uu____8717 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____8717, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____8725 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____8725 with
                                | (t1,uu____8729) ->
                                    let uu____8730 =
                                      FStar_TypeChecker_Env.new_uvar
                                        t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    Prims.fst uu____8730
                                 in
                              let uu____8733 =
                                FStar_TypeChecker_Env.new_uvar
                                  t.FStar_Syntax_Syntax.pos pattern_vars1 kk
                                 in
                              (match uu____8733 with
                               | (t',tm_u1) ->
                                   let uu____8740 = destruct_flex_t t'  in
                                   (match uu____8740 with
                                    | (uu____8760,u1,k1,uu____8763) ->
                                        let sol =
                                          let uu____8791 =
                                            let uu____8796 =
                                              u_abs wl k all_formals t'  in
                                            ((u, k), uu____8796)  in
                                          TERM uu____8791  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____8856 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____8856 with
                               | None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | None  -> true
                                     | Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____8885  ->
                                                 match uu____8885 with
                                                 | (x,uu____8889) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (Prims.fst y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (Prims.fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____8895 =
                                        let uu____8896 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____8896  in
                                      if uu____8895
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____8900 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____8900 formals1
                                           tl1)))
                          | uu____8906 -> failwith "Impossible"  in
                        let uu____8917 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____8917 all_formals args)
                in
             let solve_both_pats wl1 uu____8965 uu____8966 r =
               match (uu____8965, uu____8966) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9120 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____9120
                   then
                     let uu____9124 = solve_prob orig None [] wl1  in
                     solve env uu____9124
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____9139 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____9139
                       then
                         let uu____9140 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____9141 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____9142 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____9143 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____9144 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9140 uu____9141 uu____9142 uu____9143
                           uu____9144
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____9186 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____9186 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9194 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____9194 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9222 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9222
                                     in
                                  let uu____9223 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____9223 k3)
                           else
                             (let uu____9226 =
                                let uu____9227 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____9228 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____9229 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitution"
                                  uu____9227 uu____9228 uu____9229
                                 in
                              failwith uu____9226)
                          in
                       let uu____9230 =
                         let uu____9234 =
                           let uu____9240 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals_comp uu____9240
                            in
                         match uu____9234 with
                         | (bs,c_k1') ->
                             let uu____9252 =
                               let uu____9258 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals_comp
                                 uu____9258
                                in
                             (match uu____9252 with
                              | (cs,c_k2') ->
                                  let k1' =
                                    FStar_TypeChecker_Env.result_typ
                                      wl1.tcenv c_k1'
                                     in
                                  let k2' =
                                    FStar_TypeChecker_Env.result_typ
                                      wl1.tcenv c_k2'
                                     in
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____9275 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_48  ->
                                         FStar_TypeChecker_Common.TProb _0_48)
                                      uu____9275
                                     in
                                  let uu____9280 =
                                    let uu____9283 =
                                      let uu____9284 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____9284.FStar_Syntax_Syntax.n  in
                                    let uu____9287 =
                                      let uu____9288 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____9288.FStar_Syntax_Syntax.n  in
                                    (uu____9283, uu____9287)  in
                                  (match uu____9280 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9294,uu____9295) ->
                                       (k1', [sub_prob])
                                   | (uu____9297,FStar_Syntax_Syntax.Tm_type
                                      uu____9298) -> (k2', [sub_prob])
                                   | uu____9300 ->
                                       let uu____9303 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____9303 with
                                        | (t,uu____9310) ->
                                            let uu____9311 =
                                              FStar_TypeChecker_Env.new_uvar
                                                r zs t
                                               in
                                            (match uu____9311 with
                                             | (k_zs,uu____9318) ->
                                                 let kprob =
                                                   let uu____9320 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_49  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_49) uu____9320
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____9230 with
                       | (k_u',sub_probs) ->
                           let uu____9330 =
                             let uu____9334 =
                               let uu____9335 =
                                 FStar_TypeChecker_Env.new_uvar r zs k_u'  in
                               FStar_All.pipe_left Prims.fst uu____9335  in
                             let uu____9340 =
                               let uu____9341 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____9341  in
                             let uu____9342 =
                               let uu____9343 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____9343  in
                             (uu____9334, uu____9340, uu____9342)  in
                           (match uu____9330 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs wl1 knew1 xs1 u_zs  in
                                let uu____9348 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____9348 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____9372 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____9372
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 =
                                             u_abs wl1 knew2 ys1 u_zs  in
                                           let uu____9379 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____9379 with
                                           | (occurs_ok1,msg1) ->
                                               if
                                                 Prims.op_Negation occurs_ok1
                                               then
                                                 giveup_or_defer1 orig
                                                   "flex-flex: failed occurs check"
                                               else
                                                 (let sol2 =
                                                    TERM ((u2, k2), sub2)  in
                                                  let wl2 =
                                                    solve_prob orig None
                                                      [sol1; sol2] wl1
                                                     in
                                                  solve env
                                                    (attempt sub_probs wl2))))))))
                in
             let solve_one_pat uu____9431 uu____9432 =
               match (uu____9431, uu____9432) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____9536 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____9536
                     then
                       let uu____9537 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9538 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____9537 uu____9538
                     else ());
                    (let uu____9540 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____9540
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____9550  ->
                              fun uu____9551  ->
                                match (uu____9550, uu____9551) with
                                | ((a,uu____9561),(t21,uu____9563)) ->
                                    let uu____9568 =
                                      let uu____9571 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____9571
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____9568
                                      (fun _0_50  ->
                                         FStar_TypeChecker_Common.TProb _0_50))
                           xs args2
                          in
                       let guard =
                         let uu____9575 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____9575  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____9585 = occurs_check env wl (u1, k1) t21  in
                        match uu____9585 with
                        | (occurs_ok,uu____9594) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____9599 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____9599
                            then
                              let sol =
                                let uu____9601 =
                                  let uu____9606 = u_abs wl k1 xs t21  in
                                  ((u1, k1), uu____9606)  in
                                TERM uu____9601  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____9619 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____9619
                               then
                                 let uu____9620 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____9620 with
                                 | (sol,(uu____9634,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____9644 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____9644
                                       then
                                         let uu____9645 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____9645
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____9650 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____9652 = lhs  in
             match uu____9652 with
             | (t1,u1,k1,args1) ->
                 let uu____9657 = rhs  in
                 (match uu____9657 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1  in
                      let maybe_pat_vars2 = pat_vars env [] args2  in
                      let r = t2.FStar_Syntax_Syntax.pos  in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (Some xs,Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (Some xs,None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (None ,Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____9683 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____9689 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____9689 with
                              | (sol,uu____9696) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____9699 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____9699
                                    then
                                      let uu____9700 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____9700
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____9705 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____9707 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____9707
        then
          let uu____9708 = solve_prob orig None [] wl  in
          solve env uu____9708
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____9712 = FStar_Util.physical_equality t1 t2  in
           if uu____9712
           then
             let uu____9713 = solve_prob orig None [] wl  in
             solve env uu____9713
           else
             ((let uu____9716 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____9716
               then
                 let uu____9717 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____9717
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar _,_)
                 |(_,FStar_Syntax_Syntax.Tm_bvar _) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___125_9763 =
                     match uu___125_9763 with
                     | [] -> c
                     | bs ->
                         let uu____9777 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____9777
                      in
                   let uu____9791 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____9791 with
                    | ((bs11,c11),(bs21,c21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let c12 =
                                   FStar_Syntax_Subst.subst_comp subst1 c11
                                    in
                                 let c22 =
                                   FStar_Syntax_Subst.subst_comp subst1 c21
                                    in
                                 let rel =
                                   let uu____9877 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____9877
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____9879 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_51  ->
                                      FStar_TypeChecker_Common.CProb _0_51)
                                   uu____9879))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___126_9956 =
                     match uu___126_9956 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____9995 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____9995 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10078 =
                                   let uu____10081 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____10082 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____10081
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10082 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_52  ->
                                      FStar_TypeChecker_Common.TProb _0_52)
                                   uu____10078))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10097 -> true
                     | uu____10112 -> false  in
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
                   let uu____10140 =
                     let uu____10151 = maybe_eta t1  in
                     let uu____10156 = maybe_eta t2  in
                     (uu____10151, uu____10156)  in
                   (match uu____10140 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___154_10187 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___154_10187.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___154_10187.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___154_10187.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___154_10187.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___154_10187.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___154_10187.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___154_10187.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___154_10187.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10220 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____10220
                        then
                          let uu____10221 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____10221 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10226 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10237,FStar_Syntax_Syntax.Tm_refine uu____10238) ->
                   let uu____10247 = as_refinement env wl t1  in
                   (match uu____10247 with
                    | (x1,phi1) ->
                        let uu____10252 = as_refinement env wl t2  in
                        (match uu____10252 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10258 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_53  ->
                                    FStar_TypeChecker_Common.TProb _0_53)
                                 uu____10258
                                in
                             let x11 = FStar_Syntax_Syntax.freshen_bv x1  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x11)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let env1 = FStar_TypeChecker_Env.push_bv env x11
                                in
                             let mk_imp1 imp phi12 phi22 =
                               let uu____10291 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____10291
                                 (guard_on_element problem x11)
                                in
                             let fallback uu____10295 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp1 FStar_Syntax_Util.mk_iff phi11
                                     phi21
                                 else
                                   mk_imp1 FStar_Syntax_Util.mk_imp phi11
                                     phi21
                                  in
                               let guard =
                                 let uu____10301 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____10301 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10308 =
                                   let uu____10311 =
                                     let uu____10312 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____10312 :: (p_scope orig)  in
                                   mk_problem uu____10311 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____10308
                                  in
                               let uu____10315 =
                                 solve env1
                                   (let uu___155_10316 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___155_10316.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___155_10316.smt_ok);
                                      tcenv = (uu___155_10316.tcenv)
                                    })
                                  in
                               (match uu____10315 with
                                | Failed uu____10320 -> fallback ()
                                | Success uu____10323 ->
                                    let guard =
                                      let uu____10327 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst
                                         in
                                      let uu____10330 =
                                        let uu____10331 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst
                                           in
                                        FStar_All.pipe_right uu____10331
                                          (guard_on_element problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____10327
                                        uu____10330
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___156_10338 = wl1  in
                                      {
                                        attempting =
                                          (uu___156_10338.attempting);
                                        wl_deferred =
                                          (uu___156_10338.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___156_10338.defer_ok);
                                        smt_ok = (uu___156_10338.smt_ok);
                                        tcenv = (uu___156_10338.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_uvar
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_uvar
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_app
                    ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_))
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   let uu____10392 = destruct_flex_t t1  in
                   let uu____10393 = destruct_flex_t t2  in
                   flex_flex1 orig uu____10392 uu____10393
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____10409 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____10409 t2 wl
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,FStar_Syntax_Syntax.Tm_type
                  _)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_type
                   _)
                  |(FStar_Syntax_Syntax.Tm_uvar
                    _,FStar_Syntax_Syntax.Tm_arrow _)
                   |(FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                        FStar_Syntax_Syntax.tk = _;
                        FStar_Syntax_Syntax.pos = _;
                        FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_arrow
                     _)
                   ->
                   solve_t' env
                     (let uu___157_10458 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___157_10458.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___157_10458.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___157_10458.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___157_10458.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___157_10458.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___157_10458.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___157_10458.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___157_10458.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___157_10458.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar _,_)
                 |(FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_),_)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____10476 =
                        let uu____10477 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____10477  in
                      if uu____10476
                      then
                        let uu____10478 =
                          FStar_All.pipe_left
                            (fun _0_55  ->
                               FStar_TypeChecker_Common.TProb _0_55)
                            (let uu___158_10481 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___158_10481.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___158_10481.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___158_10481.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___158_10481.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___158_10481.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___158_10481.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___158_10481.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___158_10481.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___158_10481.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____10482 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____10478 uu____10482 t2
                          wl
                      else
                        (let uu____10487 = base_and_refinement env wl t2  in
                         match uu____10487 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____10517 =
                                    FStar_All.pipe_left
                                      (fun _0_56  ->
                                         FStar_TypeChecker_Common.TProb _0_56)
                                      (let uu___159_10520 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___159_10520.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___159_10520.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___159_10520.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___159_10520.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___159_10520.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___159_10520.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___159_10520.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___159_10520.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___159_10520.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____10521 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____10517
                                    uu____10521 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___160_10536 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___160_10536.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___160_10536.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl = guard_on_element problem y' phi
                                     in
                                  let base_prob =
                                    let uu____10539 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_57  ->
                                         FStar_TypeChecker_Common.TProb _0_57)
                                      uu____10539
                                     in
                                  let guard =
                                    let uu____10547 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____10547
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (_,FStar_Syntax_Syntax.Tm_uvar _)
                 |(_,FStar_Syntax_Syntax.Tm_app
                   ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
                      FStar_Syntax_Syntax.tk = _;
                      FStar_Syntax_Syntax.pos = _;
                      FStar_Syntax_Syntax.vars = _;_},_))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____10569 = base_and_refinement env wl t1  in
                      match uu____10569 with
                      | (t_base,uu____10580) ->
                          solve_t env
                            (let uu___161_10595 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___161_10595.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___161_10595.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___161_10595.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___161_10595.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___161_10595.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___161_10595.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___161_10595.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___161_10595.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____10598,uu____10599) ->
                   let t21 =
                     let uu____10607 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____10607  in
                   solve_t env
                     (let uu___162_10620 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_10620.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___162_10620.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___162_10620.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_10620.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_10620.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_10620.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_10620.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_10620.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_10620.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____10621,FStar_Syntax_Syntax.Tm_refine uu____10622) ->
                   let t11 =
                     let uu____10630 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____10630  in
                   solve_t env
                     (let uu___163_10643 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_10643.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_10643.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___163_10643.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___163_10643.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_10643.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_10643.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_10643.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_10643.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_10643.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match _,_)
                 |(FStar_Syntax_Syntax.Tm_uinst _,_)
                  |(FStar_Syntax_Syntax.Tm_name _,_)
                   |(FStar_Syntax_Syntax.Tm_constant _,_)
                    |(FStar_Syntax_Syntax.Tm_fvar _,_)
                     |(FStar_Syntax_Syntax.Tm_app _,_)
                      |(_,FStar_Syntax_Syntax.Tm_match _)
                       |(_,FStar_Syntax_Syntax.Tm_uinst _)
                        |(_,FStar_Syntax_Syntax.Tm_name _)
                         |(_,FStar_Syntax_Syntax.Tm_constant _)
                          |(_,FStar_Syntax_Syntax.Tm_fvar _)
                           |(_,FStar_Syntax_Syntax.Tm_app _)
                   ->
                   let head1 =
                     let uu____10673 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____10673 Prims.fst  in
                   let head2 =
                     let uu____10704 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____10704 Prims.fst  in
                   let uu____10732 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____10732
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____10741 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____10741
                      then
                        let guard =
                          let uu____10748 =
                            let uu____10749 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____10749 = FStar_Syntax_Util.Equal  in
                          if uu____10748
                          then None
                          else
                            (let uu____10752 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_58  -> Some _0_58)
                               uu____10752)
                           in
                        let uu____10754 = solve_prob orig guard [] wl  in
                        solve env uu____10754
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____10758,uu____10759),uu____10760) ->
                   solve_t' env
                     (let uu___164_10779 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_10779.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_10779.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___164_10779.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___164_10779.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_10779.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_10779.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_10779.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_10779.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_10779.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____10782,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____10784,uu____10785)) ->
                   solve_t' env
                     (let uu___165_10804 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___165_10804.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___165_10804.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___165_10804.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___165_10804.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___165_10804.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___165_10804.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___165_10804.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___165_10804.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___165_10804.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____10817 =
                     let uu____10818 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____10819 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____10818
                       uu____10819
                      in
                   failwith uu____10817
               | uu____10820 -> giveup env "head tag mismatch" orig)))

and solve_c :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2 None reason  in
        let solve_eq nct1 nct2 =
          (let uu____10852 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____10852
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____10860  ->
                  fun uu____10861  ->
                    match (uu____10860, uu____10861) with
                    | ((a1,uu____10871),(a2,uu____10873)) ->
                        let uu____10878 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_59  -> FStar_TypeChecker_Common.TProb _0_59)
                          uu____10878)
               (FStar_List.append nct1.FStar_TypeChecker_Env.nct_indices
                  [nct1.FStar_TypeChecker_Env.nct_result;
                  nct1.FStar_TypeChecker_Env.nct_wp])
               (FStar_List.append nct2.FStar_TypeChecker_Env.nct_indices
                  [nct2.FStar_TypeChecker_Env.nct_result;
                  nct2.FStar_TypeChecker_Env.nct_wp])
              in
           let guard =
             let uu____10892 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____10892  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub nct1 edge nct2 =
          let r = FStar_TypeChecker_Env.get_range env  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then
            let uu____10909 = edge.FStar_TypeChecker_Env.mlift nct1  in
            solve_eq uu____10909 nct2
          else
            (let nct1orig = nct1  in
             let nct11 = edge.FStar_TypeChecker_Env.mlift nct1  in
             (let uu____10918 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____10918
              then
                let uu____10919 =
                  let uu____10920 =
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env
                      nct1orig
                     in
                  FStar_Syntax_Print.comp_to_string uu____10920  in
                let uu____10921 =
                  let uu____10922 =
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct11
                     in
                  FStar_Syntax_Print.comp_to_string uu____10922  in
                let uu____10923 =
                  let uu____10924 =
                    FStar_TypeChecker_Env.normal_comp_typ_as_comp env nct2
                     in
                  FStar_Syntax_Print.comp_to_string uu____10924  in
                FStar_Util.print3 "solve_sub %s (lifted to %s) %s\n"
                  uu____10919 uu____10921 uu____10923
              else ());
             (let c2_decl =
                FStar_TypeChecker_Env.get_effect_decl env
                  nct2.FStar_TypeChecker_Env.nct_name
                 in
              let wp2_stronger_than_wp1 =
                if env.FStar_TypeChecker_Env.lax
                then FStar_Syntax_Util.t_true
                else
                  (let is_null_wp_2 =
                     FStar_All.pipe_right
                       nct2.FStar_TypeChecker_Env.nct_flags
                       (FStar_Util.for_some
                          (fun uu___127_10931  ->
                             match uu___127_10931 with
                             | FStar_Syntax_Syntax.TOTAL 
                               |FStar_Syntax_Syntax.MLEFFECT 
                                |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                             | uu____10932 -> false))
                      in
                   if is_null_wp_2
                   then
                     ((let uu____10934 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10934
                       then FStar_Util.print_string "Using trivial wp ... \n"
                       else ());
                      (let uu____10936 =
                         let uu____10939 =
                           let uu____10940 =
                             let uu____10950 =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 nct2.FStar_TypeChecker_Env.nct_univs env
                                 c2_decl c2_decl.FStar_Syntax_Syntax.trivial
                                in
                             (uu____10950,
                               (FStar_List.append
                                  nct11.FStar_TypeChecker_Env.nct_indices
                                  [nct11.FStar_TypeChecker_Env.nct_result;
                                  nct11.FStar_TypeChecker_Env.nct_wp]))
                              in
                           FStar_Syntax_Syntax.Tm_app uu____10940  in
                         FStar_Syntax_Syntax.mk uu____10939  in
                       uu____10936
                         (Some
                            (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                         r))
                   else
                     (let uu____10969 =
                        let uu____10972 =
                          let uu____10973 =
                            let uu____10983 =
                              FStar_TypeChecker_Env.inst_effect_fun_with
                                nct2.FStar_TypeChecker_Env.nct_univs env
                                c2_decl c2_decl.FStar_Syntax_Syntax.stronger
                               in
                            (uu____10983,
                              (FStar_List.append
                                 nct2.FStar_TypeChecker_Env.nct_indices
                                 [nct11.FStar_TypeChecker_Env.nct_result;
                                 nct2.FStar_TypeChecker_Env.nct_wp;
                                 nct11.FStar_TypeChecker_Env.nct_wp]))
                             in
                          FStar_Syntax_Syntax.Tm_app uu____10973  in
                        FStar_Syntax_Syntax.mk uu____10972  in
                      uu____10969
                        (Some
                           (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                        r))
                 in
              let base_prob =
                let uu____11002 =
                  sub_prob (Prims.fst nct11.FStar_TypeChecker_Env.nct_result)
                    problem.FStar_TypeChecker_Common.relation
                    (Prims.fst nct2.FStar_TypeChecker_Env.nct_result)
                    "result type"
                   in
                FStar_All.pipe_left
                  (fun _0_60  -> FStar_TypeChecker_Common.TProb _0_60)
                  uu____11002
                 in
              let index_probs =
                FStar_List.map2
                  (fun i  ->
                     fun j  ->
                       let uu____11023 =
                         sub_prob (Prims.fst i) FStar_TypeChecker_Common.EQ
                           (Prims.fst j) "computation index"
                          in
                       FStar_All.pipe_left
                         (fun _0_61  -> FStar_TypeChecker_Common.TProb _0_61)
                         uu____11023) nct11.FStar_TypeChecker_Env.nct_indices
                  nct2.FStar_TypeChecker_Env.nct_indices
                 in
              let univ_probs =
                let mk_type u =
                  (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u))
                    None FStar_Range.dummyRange
                   in
                FStar_List.map2
                  (fun u  ->
                     fun u'  ->
                       let uu____11046 =
                         let uu____11049 = mk_type u  in
                         let uu____11050 = mk_type u'  in
                         sub_prob uu____11049 FStar_TypeChecker_Common.EQ
                           uu____11050 "computation universes"
                          in
                       FStar_All.pipe_left
                         (fun _0_62  -> FStar_TypeChecker_Common.TProb _0_62)
                         uu____11046) nct11.FStar_TypeChecker_Env.nct_univs
                  nct2.FStar_TypeChecker_Env.nct_univs
                 in
              let wl1 =
                let uu____11054 =
                  let uu____11056 =
                    let uu____11059 =
                      FStar_All.pipe_right (p_guard base_prob) Prims.fst  in
                    FStar_Syntax_Util.mk_conj uu____11059
                      wp2_stronger_than_wp1
                     in
                  FStar_All.pipe_left (fun _0_63  -> Some _0_63) uu____11056
                   in
                solve_prob orig uu____11054 [] wl  in
              solve env
                (attempt
                   (FStar_List.append (base_prob :: index_probs) univ_probs)
                   wl1)))
           in
        let uu____11069 = FStar_Util.physical_equality c1 c2  in
        if uu____11069
        then
          let uu____11070 = solve_prob orig None [] wl  in
          solve env uu____11070
        else
          ((let uu____11073 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____11073
            then
              let uu____11074 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____11075 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11074
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11075
            else ());
           (let uu____11077 =
              let uu____11080 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____11081 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____11080, uu____11081)  in
            match uu____11077 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11085),FStar_Syntax_Syntax.Total
                    (t2,uu____11087)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____11100 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11100 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11103,FStar_Syntax_Syntax.Total uu____11104) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11153 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11153 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11160 =
                       let uu___166_11163 = problem  in
                       let uu____11166 =
                         let uu____11167 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11167
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_11163.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11166;
                         FStar_TypeChecker_Common.relation =
                           (uu___166_11163.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___166_11163.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___166_11163.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_11163.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_11163.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_11163.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_11163.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_11163.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11160 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11172 =
                       let uu___167_11175 = problem  in
                       let uu____11178 =
                         let uu____11179 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11179
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_11175.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___167_11175.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___167_11175.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11178;
                         FStar_TypeChecker_Common.element =
                           (uu___167_11175.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_11175.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_11175.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_11175.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_11175.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_11175.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11172 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11180,FStar_Syntax_Syntax.Comp uu____11181) ->
                     let uu____11182 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____11182
                     then
                       let uu____11183 =
                         let uu____11184 =
                           FStar_TypeChecker_Env.result_typ env c11  in
                         let uu____11185 =
                           FStar_TypeChecker_Env.result_typ env c21  in
                         problem_using_guard orig uu____11184
                           problem.FStar_TypeChecker_Common.relation
                           uu____11185 None "result type"
                          in
                       solve_t env uu____11183 wl
                     else
                       (let nct1 =
                          FStar_TypeChecker_Env.comp_as_normal_comp_typ env
                            c11
                           in
                        let nct2 =
                          FStar_TypeChecker_Env.comp_as_normal_comp_typ env
                            c21
                           in
                        if
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            &&
                            (FStar_Ident.lid_equals
                               nct1.FStar_TypeChecker_Env.nct_name
                               nct2.FStar_TypeChecker_Env.nct_name)
                        then solve_eq nct1 nct2
                        else
                          ((let uu____11191 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11191
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (nct1.FStar_TypeChecker_Env.nct_name).FStar_Ident.str
                                (nct2.FStar_TypeChecker_Env.nct_name).FStar_Ident.str
                            else ());
                           (let uu____11193 =
                              FStar_TypeChecker_Env.monad_leq env
                                nct1.FStar_TypeChecker_Env.nct_name
                                nct2.FStar_TypeChecker_Env.nct_name
                               in
                            match uu____11193 with
                            | None  ->
                                let uu____11195 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      nct1.FStar_TypeChecker_Env.nct_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        nct2.FStar_TypeChecker_Env.nct_name))
                                    &&
                                    (let uu____11196 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         (Prims.fst
                                            nct2.FStar_TypeChecker_Env.nct_result)
                                        in
                                     FStar_TypeChecker_Env.non_informative
                                       env uu____11196)
                                   in
                                if uu____11195
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (nct1.FStar_TypeChecker_Env.nct_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (nct2.FStar_TypeChecker_Env.nct_name);
                                      FStar_TypeChecker_Env.mlift =
                                        (fun nct  ->
                                           let uu___168_11201 = nct  in
                                           {
                                             FStar_TypeChecker_Env.nct_name =
                                               (nct2.FStar_TypeChecker_Env.nct_name);
                                             FStar_TypeChecker_Env.nct_univs
                                               =
                                               (uu___168_11201.FStar_TypeChecker_Env.nct_univs);
                                             FStar_TypeChecker_Env.nct_indices
                                               =
                                               (uu___168_11201.FStar_TypeChecker_Env.nct_indices);
                                             FStar_TypeChecker_Env.nct_result
                                               =
                                               (uu___168_11201.FStar_TypeChecker_Env.nct_result);
                                             FStar_TypeChecker_Env.nct_wp =
                                               (uu___168_11201.FStar_TypeChecker_Env.nct_wp);
                                             FStar_TypeChecker_Env.nct_flags
                                               =
                                               (uu___168_11201.FStar_TypeChecker_Env.nct_flags)
                                           })
                                    }  in
                                  solve_sub nct1 edge nct2
                                else
                                  (let uu____11203 =
                                     let uu____11204 =
                                       FStar_Syntax_Print.lid_to_string
                                         nct1.FStar_TypeChecker_Env.nct_name
                                        in
                                     let uu____11205 =
                                       FStar_Syntax_Print.lid_to_string
                                         nct2.FStar_TypeChecker_Env.nct_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11204 uu____11205
                                      in
                                   giveup env uu____11203 orig)
                            | Some edge -> solve_sub nct1 edge nct2))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11210 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11230  ->
              match uu____11230 with
              | (uu____11241,uu____11242,u,uu____11244,uu____11245,uu____11246)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____11210 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11275 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____11275 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____11285 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____11297  ->
                match uu____11297 with
                | (u1,u2) ->
                    let uu____11302 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____11303 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____11302 uu____11303))
         in
      FStar_All.pipe_right uu____11285 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____11315,[])) -> "{}"
      | uu____11328 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____11338 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____11338
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____11341 =
              FStar_List.map
                (fun uu____11345  ->
                   match uu____11345 with
                   | (uu____11348,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____11341 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____11352 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____11352 imps
  
let guard_of_guard_formula :
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
  
let guard_form :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun g  -> g.FStar_TypeChecker_Env.guard_f 
let is_trivial : FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____11372;
        FStar_TypeChecker_Env.implicits = uu____11373;_} -> true
    | uu____11387 -> false
  
let trivial_guard : FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let abstract_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv ->
      FStar_TypeChecker_Env.guard_t Prims.option ->
        FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun x  ->
      fun g  ->
        match g with
        | None |Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = _;
            FStar_TypeChecker_Env.univ_ineqs = _;
            FStar_TypeChecker_Env.implicits = _;_} -> g
        | Some g1 ->
            let f =
              match g1.FStar_TypeChecker_Env.guard_f with
              | FStar_TypeChecker_Common.NonTrivial f -> f
              | uu____11417 -> failwith "impossible"  in
            let uu____11418 =
              let uu___169_11419 = g1  in
              let uu____11420 =
                let uu____11421 =
                  let uu____11422 =
                    let uu____11426 = FStar_Syntax_Syntax.mk_binder x  in
                    [uu____11426]  in
                  let uu____11427 =
                    FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0  in
                  mk_abs env uu____11422 f uu____11427  in
                FStar_All.pipe_left
                  (fun _0_64  -> FStar_TypeChecker_Common.NonTrivial _0_64)
                  uu____11421
                 in
              {
                FStar_TypeChecker_Env.guard_f = uu____11420;
                FStar_TypeChecker_Env.deferred =
                  (uu___169_11419.FStar_TypeChecker_Env.deferred);
                FStar_TypeChecker_Env.univ_ineqs =
                  (uu___169_11419.FStar_TypeChecker_Env.univ_ineqs);
                FStar_TypeChecker_Env.implicits =
                  (uu___169_11419.FStar_TypeChecker_Env.implicits)
              }  in
            Some uu____11418
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___170_11435 = g  in
          let uu____11436 =
            let uu____11437 =
              let uu____11438 =
                let uu____11441 =
                  let uu____11442 =
                    let uu____11452 =
                      let uu____11454 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____11454]  in
                    (f, uu____11452)  in
                  FStar_Syntax_Syntax.Tm_app uu____11442  in
                FStar_Syntax_Syntax.mk uu____11441  in
              uu____11438
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_65  -> FStar_TypeChecker_Common.NonTrivial _0_65)
              uu____11437
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____11436;
            FStar_TypeChecker_Env.deferred =
              (uu___170_11435.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___170_11435.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___170_11435.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____11467 ->
        failwith "impossible"
  
let conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g)
        |(g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____11477 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____11477
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____11486 -> FStar_TypeChecker_Common.NonTrivial t
  
let imp_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) ->
          FStar_TypeChecker_Common.Trivial
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let imp = FStar_Syntax_Util.mk_imp f1 f2  in check_trivial imp
  
let binop_guard :
  (FStar_TypeChecker_Common.guard_formula ->
     FStar_TypeChecker_Common.guard_formula ->
       FStar_TypeChecker_Common.guard_formula)
    ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun f  ->
    fun g1  ->
      fun g2  ->
        let uu____11517 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____11517;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append
                (Prims.fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (Prims.fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (Prims.snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (Prims.snd g2.FStar_TypeChecker_Env.univ_ineqs)));
          FStar_TypeChecker_Env.implicits =
            (FStar_List.append g1.FStar_TypeChecker_Env.implicits
               g2.FStar_TypeChecker_Env.implicits)
        }
  
let conj_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2 
let imp_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2 
let close_guard :
  FStar_Syntax_Syntax.binders ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun binders  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___171_11555 = g  in
          let uu____11556 =
            let uu____11557 = FStar_Syntax_Util.close_forall binders f  in
            FStar_All.pipe_right uu____11557
              (fun _0_66  -> FStar_TypeChecker_Common.NonTrivial _0_66)
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____11556;
            FStar_TypeChecker_Env.deferred =
              (uu___171_11555.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___171_11555.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___171_11555.FStar_TypeChecker_Env.implicits)
          }
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____11595 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____11595
    then
      let uu____11596 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____11597 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11596
        (rel_to_string rel) uu____11597
    else "TOP"  in
  let p = new_problem env lhs rel rhs elt loc reason  in p 
let new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____11617 =
              let uu____11619 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_67  -> Some _0_67) uu____11619  in
            FStar_Syntax_Syntax.new_bv uu____11617 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____11625 =
              let uu____11627 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_68  -> Some _0_68) uu____11627  in
            let uu____11629 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____11625 uu____11629  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         FStar_TypeChecker_Common.deferred Prims.option)
        -> FStar_TypeChecker_Common.deferred Prims.option
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs1 =
          let uu____11652 = FStar_Options.eager_inference ()  in
          if uu____11652
          then
            let uu___172_11653 = probs  in
            {
              attempting = (uu___172_11653.attempting);
              wl_deferred = (uu___172_11653.wl_deferred);
              ctr = (uu___172_11653.ctr);
              defer_ok = false;
              smt_ok = (uu___172_11653.smt_ok);
              tcenv = (uu___172_11653.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____11664 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____11664
              then
                let uu____11665 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____11665
              else ());
             err (d, s))
  
let simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____11675 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____11675
            then
              let uu____11676 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____11676
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____11680 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____11680
             then
               let uu____11681 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____11681
             else ());
            (let f2 =
               let uu____11684 =
                 let uu____11685 = FStar_Syntax_Util.unmeta f1  in
                 uu____11685.FStar_Syntax_Syntax.n  in
               match uu____11684 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____11689 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___173_11690 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___173_11690.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___173_11690.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___173_11690.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred Prims.option ->
        FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____11705 =
              let uu____11706 =
                let uu____11707 =
                  let uu____11708 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst  in
                  FStar_All.pipe_right uu____11708
                    (fun _0_69  -> FStar_TypeChecker_Common.NonTrivial _0_69)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____11707;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____11706  in
            FStar_All.pipe_left (fun _0_70  -> Some _0_70) uu____11705
  
let try_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____11732 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____11732
         then
           let uu____11733 = FStar_Syntax_Print.term_to_string t1  in
           let uu____11734 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "try_teq of %s and %s\n" uu____11733 uu____11734
         else ());
        (let prob =
           let uu____11737 =
             let uu____11740 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
               uu____11740
              in
           FStar_All.pipe_left
             (fun _0_71  -> FStar_TypeChecker_Common.TProb _0_71) uu____11737
            in
         let g =
           let uu____11745 =
             let uu____11747 = singleton env prob  in
             solve_and_commit env uu____11747 (fun uu____11748  -> None)  in
           FStar_All.pipe_left (with_guard env prob) uu____11745  in
         g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____11762 = try_teq env t1 t2  in
        match uu____11762 with
        | None  ->
            let uu____11764 =
              let uu____11765 =
                let uu____11768 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____11769 = FStar_TypeChecker_Env.get_range env  in
                (uu____11768, uu____11769)  in
              FStar_Errors.Error uu____11765  in
            Prims.raise uu____11764
        | Some g ->
            ((let uu____11772 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____11772
              then
                let uu____11773 = FStar_Syntax_Print.term_to_string t1  in
                let uu____11774 = FStar_Syntax_Print.term_to_string t2  in
                let uu____11775 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____11773
                  uu____11774 uu____11775
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____11791 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____11791
           then
             let uu____11792 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____11793 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____11792
               uu____11793
           else ());
          (let uu____11795 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____11795 with
           | (prob,x) ->
               let g =
                 let uu____11803 =
                   let uu____11805 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____11805
                     (fun uu____11806  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____11803  in
               ((let uu____11812 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____11812
                 then
                   let uu____11813 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____11814 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____11815 =
                     let uu____11816 = FStar_Util.must g  in
                     guard_to_string env uu____11816  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____11813 uu____11814 uu____11815
                 else ());
                abstract_guard env x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  = fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true 
let subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____11840 = FStar_TypeChecker_Env.get_range env  in
          let uu____11841 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.report uu____11840 uu____11841
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____11853 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____11853
         then
           let uu____11854 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____11855 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____11854
             uu____11855
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____11860 =
             let uu____11863 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____11863 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_72  -> FStar_TypeChecker_Common.CProb _0_72) uu____11860
            in
         let uu____11866 =
           let uu____11868 = singleton env prob  in
           solve_and_commit env uu____11868 (fun uu____11869  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____11866)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____11888  ->
        match uu____11888 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____11913 =
                 let uu____11914 =
                   let uu____11917 =
                     let uu____11918 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____11919 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____11918 uu____11919
                      in
                   let uu____11920 = FStar_TypeChecker_Env.get_range env  in
                   (uu____11917, uu____11920)  in
                 FStar_Errors.Error uu____11914  in
               Prims.raise uu____11913)
               in
            let equiv v1 v' =
              let uu____11928 =
                let uu____11931 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____11932 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____11931, uu____11932)  in
              match uu____11928 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____11940 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____11954 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____11954 with
                      | FStar_Syntax_Syntax.U_unif uu____11958 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____11969  ->
                                    match uu____11969 with
                                    | (u,v') ->
                                        let uu____11975 = equiv v1 v'  in
                                        if uu____11975
                                        then
                                          let uu____11977 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____11977 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____11987 -> []))
               in
            let uu____11990 =
              let wl =
                let uu___174_11993 = empty_worklist env  in
                {
                  attempting = (uu___174_11993.attempting);
                  wl_deferred = (uu___174_11993.wl_deferred);
                  ctr = (uu___174_11993.ctr);
                  defer_ok = false;
                  smt_ok = (uu___174_11993.smt_ok);
                  tcenv = (uu___174_11993.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12000  ->
                      match uu____12000 with
                      | (lb,v1) ->
                          let uu____12005 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____12005 with
                           | USolved wl1 -> ()
                           | uu____12007 -> fail lb v1)))
               in
            let rec check_ineq uu____12013 =
              match uu____12013 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12020) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ
                      v0)
                     |(FStar_Syntax_Syntax.U_unif
                       _,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____12036) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12040,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12045 -> false)
               in
            let uu____12048 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12054  ->
                      match uu____12054 with
                      | (u,v1) ->
                          let uu____12059 = check_ineq (u, v1)  in
                          if uu____12059
                          then true
                          else
                            ((let uu____12062 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____12062
                              then
                                let uu____12063 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____12064 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____12063
                                  uu____12064
                              else ());
                             false)))
               in
            if uu____12048
            then ()
            else
              ((let uu____12068 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____12068
                then
                  ((let uu____12070 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12070);
                   FStar_Unionfind.rollback tx;
                   (let uu____12076 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12076))
                else ());
               (let uu____12082 =
                  let uu____12083 =
                    let uu____12086 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12086)
                     in
                  FStar_Errors.Error uu____12083  in
                Prims.raise uu____12082))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs; FStar_Unionfind.commit tx
  
let rec solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____12119 =
        match uu____12119 with
        | (d,s) ->
            let msg = explain env d s  in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____12129 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____12129
       then
         let uu____12130 = wl_to_string wl  in
         let uu____12131 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12130 uu____12131
       else ());
      (let g1 =
         let uu____12143 = solve_and_commit env wl fail  in
         match uu____12143 with
         | Some [] ->
             let uu___175_12150 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___175_12150.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___175_12150.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___175_12150.FStar_TypeChecker_Env.implicits)
             }
         | uu____12153 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___176_12156 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_12156.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_12156.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___176_12156.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___177_12182 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___177_12182.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___177_12182.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___177_12182.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____12183 =
            let uu____12184 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____12184  in
          if uu____12183
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12190 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm")
                      in
                   if uu____12190
                   then
                     let uu____12191 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____12192 =
                       let uu____12193 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12193
                        in
                     FStar_Errors.diag uu____12191 uu____12192
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc
                      in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____12202 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12202
                           then
                             let uu____12203 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____12204 =
                               let uu____12205 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12205
                                in
                             FStar_Errors.diag uu____12203 uu____12204
                           else ());
                          (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                            use_env_range_msg env vc2;
                          Some ret_g))))
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____12213 = discharge_guard' None env g true  in
      match uu____12213 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12233 = FStar_Unionfind.find u  in
      match uu____12233 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12242 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____12257 = acc  in
      match uu____12257 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12303 = hd1  in
               (match uu____12303 with
                | (uu____12310,env,u,tm,k,r) ->
                    let uu____12316 = unresolved u  in
                    if uu____12316
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____12334 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____12334
                        then
                          let uu____12335 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____12339 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____12340 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12335 uu____12339 uu____12340
                        else ());
                       (let uu____12342 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___178_12346 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___178_12346.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___178_12346.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___178_12346.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___178_12346.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___178_12346.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___178_12346.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___178_12346.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___178_12346.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___178_12346.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___178_12346.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___178_12346.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___178_12346.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___178_12346.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___178_12346.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___178_12346.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___178_12346.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___178_12346.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___178_12346.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___178_12346.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___178_12346.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___178_12346.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___178_12346.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___178_12346.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____12342 with
                        | (uu____12347,uu____12348,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___179_12351 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___179_12351.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___179_12351.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___179_12351.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____12354 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12358  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____12354 with
                              | Some g3 -> g3
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                               in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1))))
       in
    let uu___180_12373 = g  in
    let uu____12374 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___180_12373.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___180_12373.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___180_12373.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12374
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12402 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____12402 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12409 = discharge_guard env g1  in
          FStar_All.pipe_left Prims.ignore uu____12409
      | (reason,uu____12411,uu____12412,e,t,r)::uu____12416 ->
          let uu____12430 =
            let uu____12431 = FStar_Syntax_Print.term_to_string t  in
            let uu____12432 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12431 uu____12432 reason
             in
          FStar_Errors.report r uu____12430
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___181_12439 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___181_12439.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___181_12439.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___181_12439.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12457 = try_teq env t1 t2  in
        match uu____12457 with
        | None  -> false
        | Some g ->
            let uu____12460 = discharge_guard' None env g false  in
            (match uu____12460 with
             | Some uu____12464 -> true
             | None  -> false)
  