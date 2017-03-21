open Prims
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____45 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____60 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____60  in
            let uv1 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let uu____80 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app (uv1, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____80, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____113 = FStar_Syntax_Util.type_u ()  in
        match uu____113 with
        | (t_type,u) ->
            let uu____118 =
              let uu____121 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____121 t_type  in
            (match uu____118 with
             | (tt,uu____123) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____144 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____170 -> false
  
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
    match projectee with | Success _0 -> true | uu____250 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____264 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____281 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____285 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____289 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___101_300  ->
    match uu___101_300 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____313 =
    let uu____314 = FStar_Syntax_Subst.compress t  in
    uu____314.FStar_Syntax_Syntax.n  in
  match uu____313 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____331 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____335 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____331 uu____335
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____338;
         FStar_Syntax_Syntax.pos = uu____339;
         FStar_Syntax_Syntax.vars = uu____340;_},args)
      ->
      let uu____368 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____372 = FStar_Syntax_Print.term_to_string ty  in
      let uu____373 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____368 uu____372 uu____373
  | uu____374 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___102_380  ->
      match uu___102_380 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____384 =
            let uu____386 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____387 =
              let uu____389 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____390 =
                let uu____392 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____393 =
                  let uu____395 =
                    let uu____397 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____398 =
                      let uu____400 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____401 =
                        let uu____403 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____404 =
                          let uu____406 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____406]  in
                        uu____403 :: uu____404  in
                      uu____400 :: uu____401  in
                    uu____397 :: uu____398  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____395
                   in
                uu____392 :: uu____393  in
              uu____389 :: uu____390  in
            uu____386 :: uu____387  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____384
      | FStar_TypeChecker_Common.CProb p ->
          let uu____411 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____412 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____411
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____412
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___103_418  ->
      match uu___103_418 with
      | UNIV (u,t) ->
          let x =
            let uu____422 = FStar_Options.hide_uvar_nums ()  in
            if uu____422
            then "?"
            else
              (let uu____424 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____424 FStar_Util.string_of_int)
             in
          let uu____426 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____426
      | TERM ((u,uu____428),t) ->
          let x =
            let uu____433 = FStar_Options.hide_uvar_nums ()  in
            if uu____433
            then "?"
            else
              (let uu____435 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____435 FStar_Util.string_of_int)
             in
          let uu____439 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____439
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____448 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____448 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____456 =
      let uu____458 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____458
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____456 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____476 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____484  ->
            match uu____484 with
            | (x,uu____488) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____476 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____493 =
      let uu____494 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____494  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____493;
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
        let uu___129_507 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___129_507.wl_deferred);
          ctr = (uu___129_507.ctr);
          defer_ok = (uu___129_507.defer_ok);
          smt_ok;
          tcenv = (uu___129_507.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___130_532 = empty_worklist env  in
  let uu____533 = FStar_List.map Prims.snd g  in
  {
    attempting = uu____533;
    wl_deferred = (uu___130_532.wl_deferred);
    ctr = (uu___130_532.ctr);
    defer_ok = false;
    smt_ok = (uu___130_532.smt_ok);
    tcenv = (uu___130_532.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___131_545 = wl  in
        {
          attempting = (uu___131_545.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___131_545.ctr);
          defer_ok = (uu___131_545.defer_ok);
          smt_ok = (uu___131_545.smt_ok);
          tcenv = (uu___131_545.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___132_557 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___132_557.wl_deferred);
        ctr = (uu___132_557.ctr);
        defer_ok = (uu___132_557.defer_ok);
        smt_ok = (uu___132_557.smt_ok);
        tcenv = (uu___132_557.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____568 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____568
         then
           let uu____569 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____569
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___104_573  ->
    match uu___104_573 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___133_589 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___133_589.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___133_589.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___133_589.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___133_589.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___133_589.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___133_589.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___133_589.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___105_610  ->
    match uu___105_610 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_28  -> FStar_TypeChecker_Common.TProb _0_28)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_29  -> FStar_TypeChecker_Common.CProb _0_29)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___106_626  ->
      match uu___106_626 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___107_629  ->
    match uu___107_629 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___108_638  ->
    match uu___108_638 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___109_648  ->
    match uu___109_648 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___110_658  ->
    match uu___110_658 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___111_669  ->
    match uu___111_669 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___112_680  ->
    match uu___112_680 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___113_689  ->
    match uu___113_689 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_30  -> FStar_TypeChecker_Common.TProb _0_30) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_31  -> FStar_TypeChecker_Common.CProb _0_31) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____703 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____703 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____714  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____764 = next_pid ()  in
  let uu____765 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____764;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____765;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____812 = next_pid ()  in
  let uu____813 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____812;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____813;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____854 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____854;
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
        let uu____900 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____900
        then
          let uu____901 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____902 = prob_to_string env d  in
          let uu____903 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____901 uu____902 uu____903 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____908 -> failwith "impossible"  in
           let uu____909 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____917 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____918 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____917, uu____918)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____922 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____923 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____922, uu____923)
              in
           match uu____909 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___114_932  ->
            match uu___114_932 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____939 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____942),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___115_965  ->
           match uu___115_965 with
           | UNIV uu____967 -> None
           | TERM ((u,uu____971),t) ->
               let uu____975 = FStar_Unionfind.equivalent uv u  in
               if uu____975 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___116_994  ->
           match uu___116_994 with
           | UNIV (u',t) ->
               let uu____998 = FStar_Unionfind.equivalent u u'  in
               if uu____998 then Some t else None
           | uu____1002 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1009 =
        let uu____1010 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1010
         in
      FStar_Syntax_Subst.compress uu____1009
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1017 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1017
  
let norm_arg env t =
  let uu____1036 = sn env (Prims.fst t)  in (uu____1036, (Prims.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1053  ->
              match uu____1053 with
              | (x,imp) ->
                  let uu____1060 =
                    let uu___134_1061 = x  in
                    let uu____1062 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___134_1061.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___134_1061.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1062
                    }  in
                  (uu____1060, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1077 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1077
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1080 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1080
        | uu____1082 -> u2  in
      let uu____1083 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1083
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1190 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1190 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1202;
               FStar_Syntax_Syntax.pos = uu____1203;
               FStar_Syntax_Syntax.vars = uu____1204;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1225 =
                 let uu____1226 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1227 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1226
                   uu____1227
                  in
               failwith uu____1225)
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1262 =
             let uu____1263 = FStar_Syntax_Subst.compress t1'  in
             uu____1263.FStar_Syntax_Syntax.n  in
           match uu____1262 with
           | FStar_Syntax_Syntax.Tm_refine uu____1275 -> aux true t1'
           | uu____1280 -> (t11, None))
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
        let uu____1315 =
          let uu____1316 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1317 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1316
            uu____1317
           in
        failwith uu____1315
     in
  let uu____1327 = whnf env t1  in aux false uu____1327 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1336 =
        let uu____1346 = empty_worklist env  in
        base_and_refinement env uu____1346 t  in
      FStar_All.pipe_right uu____1336 Prims.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1370 = FStar_Syntax_Syntax.null_bv t  in
    (uu____1370, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____1390 = base_and_refinement env wl t  in
  match uu____1390 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____1449 =
  match uu____1449 with
  | (t_base,refopt) ->
      let uu____1463 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____1463 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___117_1487  ->
      match uu___117_1487 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1491 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1492 =
            let uu____1493 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____1493  in
          let uu____1494 =
            let uu____1495 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____1495  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1491 uu____1492
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1494
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1499 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1500 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1501 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____1499 uu____1500
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1501
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____1505 =
      let uu____1507 =
        let uu____1509 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1519  ->
                  match uu____1519 with | (uu____1523,uu____1524,x) -> x))
           in
        FStar_List.append wl.attempting uu____1509  in
      FStar_List.map (wl_prob_to_string wl) uu____1507  in
    FStar_All.pipe_right uu____1505 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1542 =
          let uu____1552 =
            let uu____1553 = FStar_Syntax_Subst.compress k  in
            uu____1553.FStar_Syntax_Syntax.n  in
          match uu____1552 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____1594 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____1594)
              else
                (let uu____1608 = FStar_Syntax_Util.abs_formals t  in
                 match uu____1608 with
                 | (ys',t1,uu____1629) ->
                     let uu____1642 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____1642))
          | uu____1663 ->
              let uu____1664 =
                let uu____1670 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____1670)  in
              ((ys, t), uu____1664)
           in
        match uu____1542 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____1725 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____1725 c  in
               let uu____1727 =
                 let uu____1734 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_32  -> FStar_Util.Inl _0_32)
                    in
                 FStar_All.pipe_right uu____1734 (fun _0_33  -> Some _0_33)
                  in
               FStar_Syntax_Util.abs ys1 t1 uu____1727)
  
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
            let uu____1785 = p_guard prob  in
            match uu____1785 with
            | (uu____1788,uv) ->
                ((let uu____1791 =
                    let uu____1792 = FStar_Syntax_Subst.compress uv  in
                    uu____1792.FStar_Syntax_Syntax.n  in
                  match uu____1791 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____1812 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____1812
                        then
                          let uu____1813 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____1814 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____1815 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____1813
                            uu____1814 uu____1815
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____1819 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___135_1822 = wl  in
                  {
                    attempting = (uu___135_1822.attempting);
                    wl_deferred = (uu___135_1822.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___135_1822.defer_ok);
                    smt_ok = (uu___135_1822.smt_ok);
                    tcenv = (uu___135_1822.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____1835 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____1835
         then
           let uu____1836 = FStar_Util.string_of_int pid  in
           let uu____1837 =
             let uu____1838 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____1838 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____1836 uu____1837
         else ());
        commit sol;
        (let uu___136_1843 = wl  in
         {
           attempting = (uu___136_1843.attempting);
           wl_deferred = (uu___136_1843.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___136_1843.defer_ok);
           smt_ok = (uu___136_1843.smt_ok);
           tcenv = (uu___136_1843.tcenv)
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
            | (uu____1872,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____1880 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____1880
             in
          (let uu____1886 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____1886
           then
             let uu____1887 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____1888 =
               let uu____1889 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____1889 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____1887 uu____1888
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____1914 =
    let uu____1918 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____1918 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____1914
    (FStar_Util.for_some
       (fun uu____1939  ->
          match uu____1939 with
          | (uv,uu____1947) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____1991 = occurs wl uk t  in Prims.op_Negation uu____1991  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____1996 =
         let uu____1997 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk)
            in
         let uu____2001 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____1997 uu____2001
          in
       Some uu____1996)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2049 = occurs_check env wl uk t  in
  match uu____2049 with
  | (occurs_ok,msg) ->
      let uu____2066 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2066, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set v1  in
  let uu____2130 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2154  ->
            fun uu____2155  ->
              match (uu____2154, uu____2155) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2198 =
                    let uu____2199 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2199  in
                  if uu____2198
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2213 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2213
                     then
                       let uu____2220 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2220)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2130 with | (isect,uu____2242) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2291  ->
          fun uu____2292  ->
            match (uu____2291, uu____2292) with
            | ((a,uu____2302),(b,uu____2304)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (Prims.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2348 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2354  ->
                match uu____2354 with
                | (b,uu____2358) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2348 then None else Some (a, (Prims.snd hd1))
  | uu____2367 -> None 
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
            let uu____2410 = pat_var_opt env seen hd1  in
            (match uu____2410 with
             | None  ->
                 ((let uu____2418 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____2418
                   then
                     let uu____2419 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2419
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2431 =
      let uu____2432 = FStar_Syntax_Subst.compress t  in
      uu____2432.FStar_Syntax_Syntax.n  in
    match uu____2431 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2448 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2510;
         FStar_Syntax_Syntax.pos = uu____2511;
         FStar_Syntax_Syntax.vars = uu____2512;_},args)
      -> (t, uv, k, args)
  | uu____2553 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____2607 = destruct_flex_t t  in
  match uu____2607 with
  | (t1,uv,k,args) ->
      let uu____2675 = pat_vars env [] args  in
      (match uu____2675 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____2731 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option *
  FStar_Syntax_Syntax.delta_depth Prims.option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____2779 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option *
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____2802 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____2806 -> false
  
let head_match : match_result -> match_result =
  fun uu___118_2809  ->
    match uu___118_2809 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____2818 -> HeadMatch
  
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
            let uu____2908 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____2908
            then FullMatch
            else
              MisMatch
                ((Some (fv_delta_depth env f)),
                  (Some (fv_delta_depth env g)))
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____2913),FStar_Syntax_Syntax.Tm_uinst (g,uu____2915)) ->
            let uu____2924 = head_matches env f g  in
            FStar_All.pipe_right uu____2924 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____2931),FStar_Syntax_Syntax.Tm_uvar (uv',uu____2933)) ->
            let uu____2958 = FStar_Unionfind.equivalent uv uv'  in
            if uu____2958 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____2966),FStar_Syntax_Syntax.Tm_refine (y,uu____2968)) ->
            let uu____2977 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____2977 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____2979),uu____2980) ->
            let uu____2985 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____2985 head_match
        | (uu____2986,FStar_Syntax_Syntax.Tm_refine (x,uu____2988)) ->
            let uu____2993 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____2993 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____2999),FStar_Syntax_Syntax.Tm_app (head',uu____3001))
            ->
            let uu____3030 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3030 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3032),uu____3033) ->
            let uu____3048 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3048 head_match
        | (uu____3049,FStar_Syntax_Syntax.Tm_app (head1,uu____3051)) ->
            let uu____3066 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3066 head_match
        | uu____3067 ->
            let uu____3070 =
              let uu____3075 = delta_depth_of_term env t11  in
              let uu____3077 = delta_depth_of_term env t21  in
              (uu____3075, uu____3077)  in
            MisMatch uu____3070
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3113 = FStar_Syntax_Util.head_and_args t  in
    match uu____3113 with
    | (head1,uu____3125) ->
        let uu____3140 =
          let uu____3141 = FStar_Syntax_Util.un_uinst head1  in
          uu____3141.FStar_Syntax_Syntax.n  in
        (match uu____3140 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3146 =
               let uu____3147 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3147 FStar_Option.isSome  in
             if uu____3146
             then
               let uu____3161 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3161 (fun _0_34  -> Some _0_34)
             else None
         | uu____3164 -> None)
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
          (let uu____3244 =
             let uu____3249 = maybe_inline t11  in
             let uu____3251 = maybe_inline t21  in (uu____3249, uu____3251)
              in
           match uu____3244 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3276 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____3276 with
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
        let uu____3291 =
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
             let uu____3299 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____3299))
           in
        (match uu____3291 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3307 -> fail r
    | uu____3312 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3337 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3367 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3382 = FStar_Syntax_Util.type_u ()  in
      match uu____3382 with
      | (t,uu____3386) ->
          let uu____3387 = new_uvar r binders t  in Prims.fst uu____3387
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3396 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____3396 Prims.fst
  
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
        let uu____3438 = head_matches env t1 t'  in
        match uu____3438 with
        | MisMatch uu____3439 -> false
        | uu____3444 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3504,imp),T (t2,uu____3507)) -> (t2, imp)
                     | uu____3524 -> failwith "Bad reconstruction") args
                args'
               in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1)))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3568  ->
                    match uu____3568 with
                    | (t2,uu____3576) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3609 = failwith "Bad reconstruction"  in
          let uu____3610 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3610 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3663))::tcs2) ->
                       aux
                         (((let uu___137_3685 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___137_3685.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___137_3685.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____3695 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___119_3726 =
                 match uu___119_3726 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____3789 = decompose1 [] bs1  in
               (rebuild, matches, uu____3789))
      | uu____3817 ->
          let rebuild uu___120_3822 =
            match uu___120_3822 with
            | [] -> t1
            | uu____3824 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___121_3843  ->
    match uu___121_3843 with
    | T (t,uu____3845) -> t
    | uu____3854 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___122_3857  ->
    match uu___122_3857 with
    | T (t,uu____3859) -> FStar_Syntax_Syntax.as_arg t
    | uu____3868 -> failwith "Impossible"
  
let imitation_sub_probs orig env scope ps qs =
  let r = p_loc orig  in
  let rel = p_rel orig  in
  let sub_prob scope1 args q =
    match q with
    | (uu____3949,variance,T (ti,mk_kind)) ->
        let k = mk_kind scope1 r  in
        let uu____3968 = new_uvar r scope1 k  in
        (match uu____3968 with
         | (gi_xs,gi) ->
             let gi_ps =
               match args with
               | [] -> gi
               | uu____3980 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (gi, args)) None r
                in
             let uu____3995 =
               let uu____3996 =
                 mk_problem scope1 orig gi_ps (vary_rel rel variance) ti None
                   "type subterm"
                  in
               FStar_All.pipe_left
                 (fun _0_35  -> FStar_TypeChecker_Common.TProb _0_35)
                 uu____3996
                in
             ((T (gi_xs, mk_kind)), uu____3995))
    | (uu____4005,uu____4006,C uu____4007) -> failwith "impos"  in
  let rec aux scope1 args qs1 =
    match qs1 with
    | [] -> ([], [], FStar_Syntax_Util.t_true)
    | q::qs2 ->
        let uu____4094 =
          match q with
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____4105;
               FStar_Syntax_Syntax.pos = uu____4106;
               FStar_Syntax_Syntax.vars = uu____4107;_})
              ->
              let uu____4122 =
                sub_prob scope1 args (bopt, variance, (T (ti, kind_type)))
                 in
              (match uu____4122 with
               | (T (gi_xs,uu____4138),prob) ->
                   let uu____4148 =
                     let uu____4149 =
                       FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                     FStar_All.pipe_left (fun _0_36  -> C _0_36) uu____4149
                      in
                   (uu____4148, [prob])
               | uu____4151 -> failwith "impossible")
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____4161;
               FStar_Syntax_Syntax.pos = uu____4162;
               FStar_Syntax_Syntax.vars = uu____4163;_})
              ->
              let uu____4178 =
                sub_prob scope1 args (bopt, variance, (T (ti, kind_type)))
                 in
              (match uu____4178 with
               | (T (gi_xs,uu____4194),prob) ->
                   let uu____4204 =
                     let uu____4205 =
                       FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt  in
                     FStar_All.pipe_left (fun _0_37  -> C _0_37) uu____4205
                      in
                   (uu____4204, [prob])
               | uu____4207 -> failwith "impossible")
          | (uu____4213,uu____4214,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
               FStar_Syntax_Syntax.tk = uu____4216;
               FStar_Syntax_Syntax.pos = uu____4217;
               FStar_Syntax_Syntax.vars = uu____4218;_})
              ->
              let components =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map
                     (fun t  ->
                        (None, INVARIANT, (T ((Prims.fst t), generic_kind)))))
                 in
              let components1 =
                (None, COVARIANT,
                  (T ((c.FStar_Syntax_Syntax.result_typ), kind_type)))
                :: components  in
              let uu____4292 =
                let uu____4297 =
                  FStar_List.map (sub_prob scope1 args) components1  in
                FStar_All.pipe_right uu____4297 FStar_List.unzip  in
              (match uu____4292 with
               | (tcs,sub_probs) ->
                   let gi_xs =
                     let uu____4326 =
                       let uu____4327 =
                         let uu____4330 = FStar_List.hd tcs  in
                         FStar_All.pipe_right uu____4330 un_T  in
                       let uu____4331 =
                         let uu____4337 = FStar_List.tl tcs  in
                         FStar_All.pipe_right uu____4337
                           (FStar_List.map arg_of_tc)
                          in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (c.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           (c.FStar_Syntax_Syntax.effect_name);
                         FStar_Syntax_Syntax.result_typ = uu____4327;
                         FStar_Syntax_Syntax.effect_args = uu____4331;
                         FStar_Syntax_Syntax.flags =
                           (c.FStar_Syntax_Syntax.flags)
                       }  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                       uu____4326
                      in
                   ((C gi_xs), sub_probs))
          | uu____4342 ->
              let uu____4349 = sub_prob scope1 args q  in
              (match uu____4349 with | (ktec,prob) -> (ktec, [prob]))
           in
        (match uu____4094 with
         | (tc,probs) ->
             let uu____4367 =
               match q with
               | (Some b,uu____4393,uu____4394) ->
                   let uu____4402 =
                     let uu____4406 =
                       FStar_Syntax_Util.arg_of_non_null_binder b  in
                     uu____4406 :: args  in
                   ((Some b), (b :: scope1), uu____4402)
               | uu____4424 -> (None, scope1, args)  in
             (match uu____4367 with
              | (bopt,scope2,args1) ->
                  let uu____4467 = aux scope2 args1 qs2  in
                  (match uu____4467 with
                   | (sub_probs,tcs,f) ->
                       let f1 =
                         match bopt with
                         | None  ->
                             let uu____4488 =
                               let uu____4490 =
                                 FStar_All.pipe_right probs
                                   (FStar_List.map
                                      (fun prob  ->
                                         FStar_All.pipe_right (p_guard prob)
                                           Prims.fst))
                                  in
                               f :: uu____4490  in
                             FStar_Syntax_Util.mk_conj_l uu____4488
                         | Some b ->
                             let uu____4502 =
                               let uu____4504 =
                                 FStar_Syntax_Util.mk_forall (Prims.fst b) f
                                  in
                               let uu____4505 =
                                 FStar_All.pipe_right probs
                                   (FStar_List.map
                                      (fun prob  ->
                                         FStar_All.pipe_right (p_guard prob)
                                           Prims.fst))
                                  in
                               uu____4504 :: uu____4505  in
                             FStar_Syntax_Util.mk_conj_l uu____4502
                          in
                       ((FStar_List.append probs sub_probs), (tc :: tcs), f1))))
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
  let uu___138_4558 = p  in
  let uu____4561 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____4562 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___138_4558.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4561;
    FStar_TypeChecker_Common.relation =
      (uu___138_4558.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4562;
    FStar_TypeChecker_Common.element =
      (uu___138_4558.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___138_4558.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___138_4558.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___138_4558.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___138_4558.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___138_4558.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____4572 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____4572
            (fun _0_38  -> FStar_TypeChecker_Common.TProb _0_38)
      | FStar_TypeChecker_Common.CProb uu____4577 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____4591 = compress_prob wl pr  in
        FStar_All.pipe_right uu____4591 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4597 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____4597 with
           | (lh,uu____4610) ->
               let uu____4625 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____4625 with
                | (rh,uu____4638) ->
                    let uu____4653 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4662,FStar_Syntax_Syntax.Tm_uvar uu____4663)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4688,uu____4689)
                          ->
                          let uu____4698 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____4698 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____4738 ->
                                    let rank =
                                      let uu____4745 = is_top_level_prob prob
                                         in
                                      if uu____4745
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____4747 =
                                      let uu___139_4750 = tp  in
                                      let uu____4753 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___139_4750.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___139_4750.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___139_4750.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____4753;
                                        FStar_TypeChecker_Common.element =
                                          (uu___139_4750.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___139_4750.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___139_4750.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___139_4750.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___139_4750.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___139_4750.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____4747)))
                      | (uu____4763,FStar_Syntax_Syntax.Tm_uvar uu____4764)
                          ->
                          let uu____4773 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____4773 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____4813 ->
                                    let uu____4819 =
                                      let uu___140_4824 = tp  in
                                      let uu____4827 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___140_4824.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____4827;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___140_4824.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___140_4824.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___140_4824.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___140_4824.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___140_4824.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___140_4824.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___140_4824.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___140_4824.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____4819)))
                      | (uu____4843,uu____4844) -> (rigid_rigid, tp)  in
                    (match uu____4653 with
                     | (rank,tp1) ->
                         let uu____4855 =
                           FStar_All.pipe_right
                             (let uu___141_4858 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___141_4858.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___141_4858.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___141_4858.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___141_4858.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___141_4858.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___141_4858.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___141_4858.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___141_4858.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___141_4858.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_39  ->
                                FStar_TypeChecker_Common.TProb _0_39)
                            in
                         (rank, uu____4855))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____4864 =
            FStar_All.pipe_right
              (let uu___142_4867 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___142_4867.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___142_4867.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___142_4867.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___142_4867.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___142_4867.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___142_4867.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___142_4867.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___142_4867.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___142_4867.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_40  -> FStar_TypeChecker_Common.CProb _0_40)
             in
          (rigid_rigid, uu____4864)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option *
      FStar_TypeChecker_Common.prob Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____4899 probs =
      match uu____4899 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____4929 = rank wl hd1  in
               (match uu____4929 with
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
    match projectee with | UDeferred _0 -> true | uu____4994 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5006 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5018 -> false
  
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
                        let uu____5055 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5055 with
                        | (k,uu____5059) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5064 -> false)))
            | uu____5065 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5108 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5108 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5111 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5117 =
                     let uu____5118 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5119 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5118
                       uu____5119
                      in
                   UFailed uu____5117)
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5136 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5136 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5139 ->
                let uu____5142 =
                  let uu____5143 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____5144 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5143
                    uu____5144 msg
                   in
                UFailed uu____5142
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5151 =
                let uu____5152 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5153 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5152 uu____5153
                 in
              failwith uu____5151
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5165 = FStar_Unionfind.equivalent v1 v2  in
              if uu____5165
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____5178 = occurs_univ v1 u3  in
              if uu____5178
              then
                let uu____5179 =
                  let uu____5180 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____5181 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5180 uu____5181
                   in
                try_umax_components u11 u21 uu____5179
              else
                (let uu____5183 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____5183)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____5193 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____5193
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
  let uu____5264 = bc1  in
  match uu____5264 with
  | (bs1,mk_cod1) ->
      let uu____5289 = bc2  in
      (match uu____5289 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____5336 = FStar_Util.first_N n1 bs  in
             match uu____5336 with
             | (bs3,rest) ->
                 let uu____5350 = mk_cod rest  in (bs3, uu____5350)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____5368 =
               let uu____5372 = mk_cod1 []  in (bs1, uu____5372)  in
             let uu____5374 =
               let uu____5378 = mk_cod2 []  in (bs2, uu____5378)  in
             (uu____5368, uu____5374)
           else
             if l1 > l2
             then
               (let uu____5400 = curry l2 bs1 mk_cod1  in
                let uu____5407 =
                  let uu____5411 = mk_cod2 []  in (bs2, uu____5411)  in
                (uu____5400, uu____5407))
             else
               (let uu____5420 =
                  let uu____5424 = mk_cod1 []  in (bs1, uu____5424)  in
                let uu____5426 = curry l1 bs2 mk_cod2  in
                (uu____5420, uu____5426)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5530 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____5530
       then
         let uu____5531 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____5531
       else ());
      (let uu____5533 = next_prob probs  in
       match uu____5533 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___143_5546 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___143_5546.wl_deferred);
               ctr = (uu___143_5546.ctr);
               defer_ok = (uu___143_5546.defer_ok);
               smt_ok = (uu___143_5546.smt_ok);
               tcenv = (uu___143_5546.tcenv)
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
                  let uu____5553 = solve_flex_rigid_join env tp probs1  in
                  (match uu____5553 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____5557 = solve_rigid_flex_meet env tp probs1  in
                     match uu____5557 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____5561,uu____5562) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5571 ->
                let uu____5576 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5604  ->
                          match uu____5604 with
                          | (c,uu____5609,uu____5610) -> c < probs.ctr))
                   in
                (match uu____5576 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____5632 =
                            FStar_List.map
                              (fun uu____5638  ->
                                 match uu____5638 with
                                 | (uu____5644,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____5632
                      | uu____5647 ->
                          let uu____5652 =
                            let uu___144_5653 = probs  in
                            let uu____5654 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____5663  ->
                                      match uu____5663 with
                                      | (uu____5667,uu____5668,y) -> y))
                               in
                            {
                              attempting = uu____5654;
                              wl_deferred = rest;
                              ctr = (uu___144_5653.ctr);
                              defer_ok = (uu___144_5653.defer_ok);
                              smt_ok = (uu___144_5653.smt_ok);
                              tcenv = (uu___144_5653.tcenv)
                            }  in
                          solve env uu____5652))))

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
            let uu____5675 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____5675 with
            | USolved wl1 ->
                let uu____5677 = solve_prob orig None [] wl1  in
                solve env uu____5677
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
                  let uu____5711 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____5711 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____5714 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____5722;
                  FStar_Syntax_Syntax.pos = uu____5723;
                  FStar_Syntax_Syntax.vars = uu____5724;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____5727;
                  FStar_Syntax_Syntax.pos = uu____5728;
                  FStar_Syntax_Syntax.vars = uu____5729;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____5745 -> USolved wl

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
            ((let uu____5753 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____5753
              then
                let uu____5754 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____5754 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____5762 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____5762
         then
           let uu____5763 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____5763
         else ());
        (let uu____5765 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____5765 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____5807 = head_matches_delta env () t1 t2  in
               match uu____5807 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____5829 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____5855 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____5864 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____5865 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____5864, uu____5865)
                          | None  ->
                              let uu____5868 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____5869 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____5868, uu____5869)
                           in
                        (match uu____5855 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____5891 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_41  ->
                                    FStar_TypeChecker_Common.TProb _0_41)
                                 uu____5891
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____5914 =
                                    let uu____5920 =
                                      let uu____5923 =
                                        let uu____5926 =
                                          let uu____5927 =
                                            let uu____5932 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____5932)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____5927
                                           in
                                        FStar_Syntax_Syntax.mk uu____5926  in
                                      uu____5923 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____5945 =
                                      let uu____5947 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____5947]  in
                                    (uu____5920, uu____5945)  in
                                  Some uu____5914
                              | (uu____5956,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5958)) ->
                                  let uu____5963 =
                                    let uu____5967 =
                                      let uu____5969 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____5969]  in
                                    (t11, uu____5967)  in
                                  Some uu____5963
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5975),uu____5976) ->
                                  let uu____5981 =
                                    let uu____5985 =
                                      let uu____5987 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____5987]  in
                                    (t21, uu____5985)  in
                                  Some uu____5981
                              | uu____5992 ->
                                  let uu____5995 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____5995 with
                                   | (head1,uu____6010) ->
                                       let uu____6025 =
                                         let uu____6026 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6026.FStar_Syntax_Syntax.n  in
                                       (match uu____6025 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6033;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6035;_}
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
                                        | uu____6044 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6053) ->
                  let uu____6066 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___123_6075  ->
                            match uu___123_6075 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6080 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6080 with
                                      | (u',uu____6091) ->
                                          let uu____6106 =
                                            let uu____6107 = whnf env u'  in
                                            uu____6107.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6106 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6111) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____6127 -> false))
                                 | uu____6128 -> false)
                            | uu____6130 -> false))
                     in
                  (match uu____6066 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6151 tps =
                         match uu____6151 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6178 =
                                    let uu____6183 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____6183  in
                                  (match uu____6178 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6202 -> None)
                          in
                       let uu____6207 =
                         let uu____6212 =
                           let uu____6216 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____6216, [])  in
                         make_lower_bound uu____6212 lower_bounds  in
                       (match uu____6207 with
                        | None  ->
                            ((let uu____6223 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6223
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
                            ((let uu____6236 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6236
                              then
                                let wl' =
                                  let uu___145_6238 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___145_6238.wl_deferred);
                                    ctr = (uu___145_6238.ctr);
                                    defer_ok = (uu___145_6238.defer_ok);
                                    smt_ok = (uu___145_6238.smt_ok);
                                    tcenv = (uu___145_6238.tcenv)
                                  }  in
                                let uu____6239 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6239
                              else ());
                             (let uu____6241 =
                                solve_t env eq_prob
                                  (let uu___146_6242 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___146_6242.wl_deferred);
                                     ctr = (uu___146_6242.ctr);
                                     defer_ok = (uu___146_6242.defer_ok);
                                     smt_ok = (uu___146_6242.smt_ok);
                                     tcenv = (uu___146_6242.tcenv)
                                   })
                                 in
                              match uu____6241 with
                              | Success uu____6244 ->
                                  let wl1 =
                                    let uu___147_6246 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___147_6246.wl_deferred);
                                      ctr = (uu___147_6246.ctr);
                                      defer_ok = (uu___147_6246.defer_ok);
                                      smt_ok = (uu___147_6246.smt_ok);
                                      tcenv = (uu___147_6246.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____6248 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____6251 -> None))))
              | uu____6252 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6259 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6259
         then
           let uu____6260 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6260
         else ());
        (let uu____6262 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____6262 with
         | (u,args) ->
             let uu____6289 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____6289 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____6320 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____6320 with
                    | (h1,args1) ->
                        let uu____6348 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____6348 with
                         | (h2,uu____6361) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____6380 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____6380
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____6393 =
                                          let uu____6395 =
                                            let uu____6396 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_42  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_42) uu____6396
                                             in
                                          [uu____6395]  in
                                        Some uu____6393))
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
                                       (let uu____6418 =
                                          let uu____6420 =
                                            let uu____6421 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_43) uu____6421
                                             in
                                          [uu____6420]  in
                                        Some uu____6418))
                                  else None
                              | uu____6429 -> None))
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
                             let uu____6495 =
                               let uu____6501 =
                                 let uu____6504 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____6504  in
                               (uu____6501, m1)  in
                             Some uu____6495)
                    | (uu____6513,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6515)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6547),uu____6548) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____6579 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6613) ->
                       let uu____6626 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___124_6635  ->
                                 match uu___124_6635 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6640 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____6640 with
                                           | (u',uu____6651) ->
                                               let uu____6666 =
                                                 let uu____6667 = whnf env u'
                                                    in
                                                 uu____6667.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6666 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6671) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6687 -> false))
                                      | uu____6688 -> false)
                                 | uu____6690 -> false))
                          in
                       (match uu____6626 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____6715 tps =
                              match uu____6715 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____6756 =
                                         let uu____6763 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____6763  in
                                       (match uu____6756 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____6798 -> None)
                               in
                            let uu____6805 =
                              let uu____6812 =
                                let uu____6818 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____6818, [])  in
                              make_upper_bound uu____6812 upper_bounds  in
                            (match uu____6805 with
                             | None  ->
                                 ((let uu____6827 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____6827
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
                                 ((let uu____6846 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____6846
                                   then
                                     let wl' =
                                       let uu___148_6848 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___148_6848.wl_deferred);
                                         ctr = (uu___148_6848.ctr);
                                         defer_ok = (uu___148_6848.defer_ok);
                                         smt_ok = (uu___148_6848.smt_ok);
                                         tcenv = (uu___148_6848.tcenv)
                                       }  in
                                     let uu____6849 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____6849
                                   else ());
                                  (let uu____6851 =
                                     solve_t env eq_prob
                                       (let uu___149_6852 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___149_6852.wl_deferred);
                                          ctr = (uu___149_6852.ctr);
                                          defer_ok = (uu___149_6852.defer_ok);
                                          smt_ok = (uu___149_6852.smt_ok);
                                          tcenv = (uu___149_6852.tcenv)
                                        })
                                      in
                                   match uu____6851 with
                                   | Success uu____6854 ->
                                       let wl1 =
                                         let uu___150_6856 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___150_6856.wl_deferred);
                                           ctr = (uu___150_6856.ctr);
                                           defer_ok =
                                             (uu___150_6856.defer_ok);
                                           smt_ok = (uu___150_6856.smt_ok);
                                           tcenv = (uu___150_6856.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____6858 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____6861 -> None))))
                   | uu____6862 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____6927 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____6927
                      then
                        let uu____6928 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____6928
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst  in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___151_6960 = hd1  in
                      let uu____6961 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___151_6960.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___151_6960.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____6961
                      }  in
                    let hd21 =
                      let uu___152_6965 = hd2  in
                      let uu____6966 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___152_6965.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___152_6965.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____6966
                      }  in
                    let prob =
                      let uu____6970 =
                        let uu____6973 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____6973 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_44  -> FStar_TypeChecker_Common.TProb _0_44)
                        uu____6970
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____6981 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____6981
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____6984 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____6984 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7002 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst
                              in
                           let uu____7005 =
                             FStar_Syntax_Util.close_forall [(hd12, imp)] phi
                              in
                           FStar_Syntax_Util.mk_conj uu____7002 uu____7005
                            in
                         ((let uu____7011 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7011
                           then
                             let uu____7012 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7013 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7012 uu____7013
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7028 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7034 = aux scope env [] bs1 bs2  in
              match uu____7034 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7050 = compress_tprob wl problem  in
        solve_t' env uu____7050 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7083 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7083 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7100,uu____7101) ->
                   let may_relate head3 =
                     let uu____7116 =
                       let uu____7117 = FStar_Syntax_Util.un_uinst head3  in
                       uu____7117.FStar_Syntax_Syntax.n  in
                     match uu____7116 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7123 -> false  in
                   let uu____7124 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____7124
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
                                let uu____7140 =
                                  let uu____7141 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7141 t21
                                   in
                                FStar_Syntax_Util.mk_forall x uu____7140
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____7143 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____7143
                   else giveup env1 "head mismatch" orig
               | (uu____7145,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___153_7153 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___153_7153.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___153_7153.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___153_7153.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___153_7153.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___153_7153.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___153_7153.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___153_7153.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___153_7153.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7154,None ) ->
                   ((let uu____7161 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7161
                     then
                       let uu____7162 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7163 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____7164 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____7165 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7162
                         uu____7163 uu____7164 uu____7165
                     else ());
                    (let uu____7167 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____7167 with
                     | (head11,args1) ->
                         let uu____7193 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____7193 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7233 =
                                  let uu____7234 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____7235 = args_to_string args1  in
                                  let uu____7236 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____7237 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7234 uu____7235 uu____7236
                                    uu____7237
                                   in
                                giveup env1 uu____7233 orig
                              else
                                (let uu____7239 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7242 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____7242 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____7239
                                 then
                                   let uu____7243 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____7243 with
                                   | USolved wl2 ->
                                       let uu____7245 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____7245
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7249 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____7249 with
                                    | (base1,refinement1) ->
                                        let uu____7275 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____7275 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____7329 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____7329 with
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
                                                           (fun uu____7339 
                                                              ->
                                                              fun uu____7340 
                                                                ->
                                                                match 
                                                                  (uu____7339,
                                                                    uu____7340)
                                                                with
                                                                | ((a,uu____7350),
                                                                   (a',uu____7352))
                                                                    ->
                                                                    let uu____7357
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
                                                                    _0_45  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_45)
                                                                    uu____7357)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____7363 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                Prims.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____7363
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____7367 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___154_7400 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___154_7400.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____7420 = p  in
          match uu____7420 with
          | (((u,k),xs,c),ps,(h,uu____7431,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7480 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____7480 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____7494 = h gs_xs  in
                     let uu____7495 =
                       let uu____7502 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_46  -> FStar_Util.Inl _0_46)
                          in
                       FStar_All.pipe_right uu____7502
                         (fun _0_47  -> Some _0_47)
                        in
                     FStar_Syntax_Util.abs xs1 uu____7494 uu____7495  in
                   ((let uu____7533 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7533
                     then
                       let uu____7534 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____7535 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____7536 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____7537 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____7538 =
                         let uu____7539 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____7539
                           (FStar_String.concat ", ")
                          in
                       let uu____7542 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____7534 uu____7535 uu____7536 uu____7537
                         uu____7538 uu____7542
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___125_7560 =
          match uu___125_7560 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____7589 = p  in
          match uu____7589 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____7647 = FStar_List.nth ps i  in
              (match uu____7647 with
               | (pi,uu____7650) ->
                   let uu____7655 = FStar_List.nth xs i  in
                   (match uu____7655 with
                    | (xi,uu____7662) ->
                        let rec gs k =
                          let uu____7671 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____7671 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____7723)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____7731 = new_uvar r xs k_a  in
                                    (match uu____7731 with
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
                                         let uu____7750 = aux subst2 tl1  in
                                         (match uu____7750 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____7765 =
                                                let uu____7767 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____7767 :: gi_xs'  in
                                              let uu____7768 =
                                                let uu____7770 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____7770 :: gi_ps'  in
                                              (uu____7765, uu____7768)))
                                 in
                              aux [] bs
                           in
                        let uu____7773 =
                          let uu____7774 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____7774
                           in
                        if uu____7773
                        then None
                        else
                          (let uu____7777 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____7777 with
                           | (g_xs,uu____7784) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____7791 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 let uu____7796 =
                                   let uu____7803 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_48  -> FStar_Util.Inl _0_48)
                                      in
                                   FStar_All.pipe_right uu____7803
                                     (fun _0_49  -> Some _0_49)
                                    in
                                 FStar_Syntax_Util.abs xs uu____7791
                                   uu____7796
                                  in
                               let sub1 =
                                 let uu____7834 =
                                   let uu____7837 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____7844 =
                                     let uu____7847 =
                                       FStar_List.map
                                         (fun uu____7853  ->
                                            match uu____7853 with
                                            | (uu____7858,uu____7859,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____7847  in
                                   mk_problem (p_scope orig) orig uu____7837
                                     (p_rel orig) uu____7844 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_50  ->
                                      FStar_TypeChecker_Common.TProb _0_50)
                                   uu____7834
                                  in
                               ((let uu____7869 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____7869
                                 then
                                   let uu____7870 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____7871 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____7870 uu____7871
                                 else ());
                                (let wl2 =
                                   let uu____7874 =
                                     let uu____7876 =
                                       FStar_All.pipe_left Prims.fst
                                         (p_guard sub1)
                                        in
                                     Some uu____7876  in
                                   solve_prob orig uu____7874
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____7881 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_51  -> Some _0_51) uu____7881)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____7905 = lhs  in
          match uu____7905 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____7928 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____7928 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____7950 =
                        let uu____7976 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____7976)  in
                      Some uu____7950
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____8059 =
                           let uu____8063 =
                             let uu____8064 = FStar_Syntax_Subst.compress k
                                in
                             uu____8064.FStar_Syntax_Syntax.n  in
                           (uu____8063, args)  in
                         match uu____8059 with
                         | (uu____8071,[]) ->
                             let uu____8073 =
                               let uu____8079 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____8079)  in
                             Some uu____8073
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____8096 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____8096 with
                              | (uv1,uv_args) ->
                                  let uu____8125 =
                                    let uu____8126 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____8126.FStar_Syntax_Syntax.n  in
                                  (match uu____8125 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8133) ->
                                       let uu____8146 =
                                         pat_vars env [] uv_args  in
                                       (match uu____8146 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8160  ->
                                                      let uu____8161 =
                                                        let uu____8162 =
                                                          let uu____8163 =
                                                            let uu____8166 =
                                                              let uu____8167
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8167
                                                                Prims.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8166
                                                             in
                                                          Prims.fst
                                                            uu____8163
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8162
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8161))
                                               in
                                            let c1 =
                                              let uu____8173 =
                                                let uu____8174 =
                                                  let uu____8177 =
                                                    let uu____8178 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8178 Prims.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8177
                                                   in
                                                Prims.fst uu____8174  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8173
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____8187 =
                                                let uu____8194 =
                                                  let uu____8200 =
                                                    let uu____8201 =
                                                      let uu____8204 =
                                                        let uu____8205 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____8205
                                                          Prims.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____8204
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____8201
                                                     in
                                                  FStar_Util.Inl uu____8200
                                                   in
                                                Some uu____8194  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8187
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____8228 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8233)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____8259 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____8259
                                 (fun _0_52  -> Some _0_52)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____8278 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____8278 with
                                  | (args1,rest) ->
                                      let uu____8294 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____8294 with
                                       | (xs2,c2) ->
                                           let uu____8302 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____8302
                                             (fun uu____8313  ->
                                                match uu____8313 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____8335 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____8335 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____8381 =
                                        let uu____8384 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____8384
                                         in
                                      FStar_All.pipe_right uu____8381
                                        (fun _0_53  -> Some _0_53))
                         | uu____8392 ->
                             let uu____8396 =
                               let uu____8397 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____8401 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____8402 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____8397 uu____8401 uu____8402
                                in
                             failwith uu____8396
                          in
                       let uu____8406 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____8406
                         (fun uu____8434  ->
                            match uu____8434 with
                            | (xs1,c1) ->
                                let uu____8462 =
                                  let uu____8485 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____8485)
                                   in
                                Some uu____8462))
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
                     let uu____8557 = imitate orig env wl1 st  in
                     match uu____8557 with
                     | Failed uu____8562 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____8568 = project orig env wl1 i st  in
                      match uu____8568 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____8586 = FStar_Syntax_Util.head_and_args t21  in
                match uu____8586 with
                | (hd1,uu____8597) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____8615 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____8618 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____8618
                         then true
                         else
                           ((let uu____8621 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____8621
                             then
                               let uu____8622 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____8622
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____8630 =
                    let uu____8633 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____8633 Prims.fst  in
                  FStar_All.pipe_right uu____8630 FStar_Syntax_Free.names  in
                let uu____8664 = FStar_Util.set_is_empty fvs_hd  in
                if uu____8664
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____8673 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____8673 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____8681 =
                            let uu____8682 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____8682
                             in
                          giveup_or_defer1 orig uu____8681
                        else
                          (let uu____8684 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____8684
                           then
                             let uu____8685 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____8685
                              then
                                let uu____8686 = subterms args_lhs  in
                                imitate' orig env wl1 uu____8686
                              else
                                ((let uu____8690 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____8690
                                  then
                                    let uu____8691 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____8692 = names_to_string fvs1  in
                                    let uu____8693 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____8691 uu____8692 uu____8693
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____8698 ->
                                        let uu____8699 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____8699 t21
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
                               (let uu____8708 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____8708
                                then
                                  ((let uu____8710 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____8710
                                    then
                                      let uu____8711 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____8712 = names_to_string fvs1
                                         in
                                      let uu____8713 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____8711 uu____8712 uu____8713
                                    else ());
                                   (let uu____8715 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____8715
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
                     (let uu____8726 =
                        let uu____8727 = FStar_Syntax_Free.names t1  in
                        check_head uu____8727 t2  in
                      if uu____8726
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____8731 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____8731
                          then
                            let uu____8732 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____8732
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____8735 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____8735 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____8777 =
               match uu____8777 with
               | (t,u,k,args) ->
                   let uu____8807 = FStar_Syntax_Util.arrow_formals k  in
                   (match uu____8807 with
                    | (all_formals,uu____8818) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____8910  ->
                                        match uu____8910 with
                                        | (x,imp) ->
                                            let uu____8917 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____8917, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____8925 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____8925 with
                                | (t1,uu____8929) ->
                                    let uu____8930 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    Prims.fst uu____8930
                                 in
                              let uu____8933 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____8933 with
                               | (t',tm_u1) ->
                                   let uu____8940 = destruct_flex_t t'  in
                                   (match uu____8940 with
                                    | (uu____8960,u1,k1,uu____8963) ->
                                        let sol =
                                          let uu____8991 =
                                            let uu____8996 =
                                              u_abs k all_formals t'  in
                                            ((u, k), uu____8996)  in
                                          TERM uu____8991  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9056 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____9056 with
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
                                              (fun uu____9085  ->
                                                 match uu____9085 with
                                                 | (x,uu____9089) ->
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
                                      let uu____9095 =
                                        let uu____9096 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____9096  in
                                      if uu____9095
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9100 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9100 formals1
                                           tl1)))
                          | uu____9106 -> failwith "Impossible"  in
                        let uu____9117 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____9117 all_formals args)
                in
             let solve_both_pats wl1 uu____9165 uu____9166 r =
               match (uu____9165, uu____9166) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____9320 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____9320
                   then
                     let uu____9324 = solve_prob orig None [] wl1  in
                     solve env uu____9324
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____9339 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____9339
                       then
                         let uu____9340 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____9341 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____9342 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____9343 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____9344 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____9340 uu____9341 uu____9342 uu____9343
                           uu____9344
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____9386 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____9386 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____9394 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____9394 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____9424 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____9424
                                     in
                                  let uu____9427 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____9427 k3)
                           else
                             (let uu____9430 =
                                let uu____9431 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____9432 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____9433 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____9431 uu____9432 uu____9433
                                 in
                              failwith uu____9430)
                          in
                       let uu____9434 =
                         let uu____9440 =
                           let uu____9448 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____9448  in
                         match uu____9440 with
                         | (bs,k1') ->
                             let uu____9466 =
                               let uu____9474 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____9474  in
                             (match uu____9466 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____9495 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_54  ->
                                         FStar_TypeChecker_Common.TProb _0_54)
                                      uu____9495
                                     in
                                  let uu____9500 =
                                    let uu____9503 =
                                      let uu____9504 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____9504.FStar_Syntax_Syntax.n  in
                                    let uu____9507 =
                                      let uu____9508 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____9508.FStar_Syntax_Syntax.n  in
                                    (uu____9503, uu____9507)  in
                                  (match uu____9500 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____9516,uu____9517) ->
                                       (k1', [sub_prob])
                                   | (uu____9521,FStar_Syntax_Syntax.Tm_type
                                      uu____9522) -> (k2', [sub_prob])
                                   | uu____9526 ->
                                       let uu____9529 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____9529 with
                                        | (t,uu____9538) ->
                                            let uu____9539 = new_uvar r zs t
                                               in
                                            (match uu____9539 with
                                             | (k_zs,uu____9548) ->
                                                 let kprob =
                                                   let uu____9550 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_55  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_55) uu____9550
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____9434 with
                       | (k_u',sub_probs) ->
                           let uu____9564 =
                             let uu____9572 =
                               let uu____9573 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left Prims.fst uu____9573  in
                             let uu____9578 =
                               let uu____9581 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____9581  in
                             let uu____9584 =
                               let uu____9587 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____9587  in
                             (uu____9572, uu____9578, uu____9584)  in
                           (match uu____9564 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____9606 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____9606 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____9630 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____9630
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____9637 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____9637 with
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
             let solve_one_pat uu____9689 uu____9690 =
               match (uu____9689, uu____9690) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____9794 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____9794
                     then
                       let uu____9795 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____9796 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____9795 uu____9796
                     else ());
                    (let uu____9798 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____9798
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____9808  ->
                              fun uu____9809  ->
                                match (uu____9808, uu____9809) with
                                | ((a,uu____9819),(t21,uu____9821)) ->
                                    let uu____9826 =
                                      let uu____9829 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____9829
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____9826
                                      (fun _0_56  ->
                                         FStar_TypeChecker_Common.TProb _0_56))
                           xs args2
                          in
                       let guard =
                         let uu____9833 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p) Prims.fst)
                             sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____9833  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____9843 = occurs_check env wl (u1, k1) t21  in
                        match uu____9843 with
                        | (occurs_ok,uu____9852) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____9857 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____9857
                            then
                              let sol =
                                let uu____9859 =
                                  let uu____9864 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____9864)  in
                                TERM uu____9859  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____9877 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____9877
                               then
                                 let uu____9878 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____9878 with
                                 | (sol,(uu____9892,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____9902 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____9902
                                       then
                                         let uu____9903 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____9903
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____9908 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____9910 = lhs  in
             match uu____9910 with
             | (t1,u1,k1,args1) ->
                 let uu____9915 = rhs  in
                 (match uu____9915 with
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
                       | uu____9941 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____9947 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____9947 with
                              | (sol,uu____9954) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____9957 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____9957
                                    then
                                      let uu____9958 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____9958
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____9963 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____9965 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____9965
        then
          let uu____9966 = solve_prob orig None [] wl  in
          solve env uu____9966
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____9970 = FStar_Util.physical_equality t1 t2  in
           if uu____9970
           then
             let uu____9971 = solve_prob orig None [] wl  in
             solve env uu____9971
           else
             ((let uu____9974 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____9974
               then
                 let uu____9975 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____9975
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
                   let mk_c c uu___126_10021 =
                     match uu___126_10021 with
                     | [] -> c
                     | bs ->
                         let uu____10035 =
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____10035
                      in
                   let uu____10049 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____10049 with
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
                                   let uu____10135 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____10135
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____10137 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_57  ->
                                      FStar_TypeChecker_Common.CProb _0_57)
                                   uu____10137))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___127_10214 =
                     match uu___127_10214 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____10253 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____10253 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10336 =
                                   let uu____10339 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____10340 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____10339
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10340 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_58  ->
                                      FStar_TypeChecker_Common.TProb _0_58)
                                   uu____10336))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10355 -> true
                     | uu____10370 -> false  in
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
                   let uu____10398 =
                     let uu____10409 = maybe_eta t1  in
                     let uu____10414 = maybe_eta t2  in
                     (uu____10409, uu____10414)  in
                   (match uu____10398 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___155_10445 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___155_10445.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___155_10445.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___155_10445.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___155_10445.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___155_10445.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___155_10445.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___155_10445.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___155_10445.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____10478 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____10478
                        then
                          let uu____10479 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____10479 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____10484 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____10495,FStar_Syntax_Syntax.Tm_refine uu____10496) ->
                   let uu____10505 = as_refinement env wl t1  in
                   (match uu____10505 with
                    | (x1,phi1) ->
                        let uu____10510 = as_refinement env wl t2  in
                        (match uu____10510 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____10516 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_59  ->
                                    FStar_TypeChecker_Common.TProb _0_59)
                                 uu____10516
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
                               let uu____10549 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____10549
                                 (guard_on_element problem x11)
                                in
                             let fallback uu____10553 =
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
                                 let uu____10559 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____10559 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____10566 =
                                   let uu____10569 =
                                     let uu____10570 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____10570 :: (p_scope orig)  in
                                   mk_problem uu____10569 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_60  ->
                                      FStar_TypeChecker_Common.TProb _0_60)
                                   uu____10566
                                  in
                               let uu____10573 =
                                 solve env1
                                   (let uu___156_10574 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___156_10574.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___156_10574.smt_ok);
                                      tcenv = (uu___156_10574.tcenv)
                                    })
                                  in
                               (match uu____10573 with
                                | Failed uu____10578 -> fallback ()
                                | Success uu____10581 ->
                                    let guard =
                                      let uu____10585 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst
                                         in
                                      let uu____10588 =
                                        let uu____10589 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst
                                           in
                                        FStar_All.pipe_right uu____10589
                                          (guard_on_element problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____10585
                                        uu____10588
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___157_10596 = wl1  in
                                      {
                                        attempting =
                                          (uu___157_10596.attempting);
                                        wl_deferred =
                                          (uu___157_10596.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___157_10596.defer_ok);
                                        smt_ok = (uu___157_10596.smt_ok);
                                        tcenv = (uu___157_10596.tcenv)
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
                   let uu____10650 = destruct_flex_t t1  in
                   let uu____10651 = destruct_flex_t t2  in
                   flex_flex1 orig uu____10650 uu____10651
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
                   let uu____10667 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____10667 t2 wl
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
                     (let uu___158_10716 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___158_10716.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___158_10716.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___158_10716.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___158_10716.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___158_10716.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___158_10716.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___158_10716.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___158_10716.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___158_10716.FStar_TypeChecker_Common.rank)
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
                      let uu____10734 =
                        let uu____10735 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____10735  in
                      if uu____10734
                      then
                        let uu____10736 =
                          FStar_All.pipe_left
                            (fun _0_61  ->
                               FStar_TypeChecker_Common.TProb _0_61)
                            (let uu___159_10739 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___159_10739.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___159_10739.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___159_10739.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___159_10739.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___159_10739.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___159_10739.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___159_10739.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___159_10739.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___159_10739.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____10740 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____10736 uu____10740 t2
                          wl
                      else
                        (let uu____10745 = base_and_refinement env wl t2  in
                         match uu____10745 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____10775 =
                                    FStar_All.pipe_left
                                      (fun _0_62  ->
                                         FStar_TypeChecker_Common.TProb _0_62)
                                      (let uu___160_10778 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___160_10778.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___160_10778.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___160_10778.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___160_10778.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___160_10778.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___160_10778.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___160_10778.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___160_10778.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___160_10778.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____10779 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____10775
                                    uu____10779 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___161_10794 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___161_10794.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___161_10794.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl = guard_on_element problem y' phi
                                     in
                                  let base_prob =
                                    let uu____10797 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10797
                                     in
                                  let guard =
                                    let uu____10805 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____10805
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
                     (let uu____10827 = base_and_refinement env wl t1  in
                      match uu____10827 with
                      | (t_base,uu____10838) ->
                          solve_t env
                            (let uu___162_10853 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___162_10853.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___162_10853.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___162_10853.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___162_10853.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___162_10853.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___162_10853.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___162_10853.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___162_10853.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____10856,uu____10857) ->
                   let t21 =
                     let uu____10865 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____10865  in
                   solve_t env
                     (let uu___163_10878 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_10878.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___163_10878.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___163_10878.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___163_10878.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_10878.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_10878.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_10878.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_10878.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_10878.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____10879,FStar_Syntax_Syntax.Tm_refine uu____10880) ->
                   let t11 =
                     let uu____10888 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____10888  in
                   solve_t env
                     (let uu___164_10901 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_10901.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_10901.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___164_10901.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___164_10901.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_10901.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_10901.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_10901.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_10901.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_10901.FStar_TypeChecker_Common.rank)
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
                     let uu____10931 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____10931 Prims.fst  in
                   let head2 =
                     let uu____10962 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____10962 Prims.fst  in
                   let uu____10990 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____10990
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____10999 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____10999
                      then
                        let guard =
                          let uu____11006 =
                            let uu____11007 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____11007 = FStar_Syntax_Util.Equal  in
                          if uu____11006
                          then None
                          else
                            (let uu____11010 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_64  -> Some _0_64)
                               uu____11010)
                           in
                        let uu____11012 = solve_prob orig guard [] wl  in
                        solve env uu____11012
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____11016,uu____11017),uu____11018) ->
                   solve_t' env
                     (let uu___165_11037 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___165_11037.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___165_11037.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___165_11037.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___165_11037.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___165_11037.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___165_11037.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___165_11037.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___165_11037.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___165_11037.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11040,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____11042,uu____11043)) ->
                   solve_t' env
                     (let uu___166_11062 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___166_11062.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___166_11062.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___166_11062.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___166_11062.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___166_11062.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___166_11062.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___166_11062.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___166_11062.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___166_11062.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   let uu____11075 =
                     let uu____11076 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____11077 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____11076
                       uu____11077
                      in
                   failwith uu____11075
               | uu____11078 -> giveup env "head tag mismatch" orig)))

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
        let solve_eq c1_comp c2_comp =
          (let uu____11110 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____11110
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11118  ->
                  fun uu____11119  ->
                    match (uu____11118, uu____11119) with
                    | ((a1,uu____11129),(a2,uu____11131)) ->
                        let uu____11136 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_65  -> FStar_TypeChecker_Common.TProb _0_65)
                          uu____11136)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____11142 =
               FStar_List.map
                 (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____11142  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____11162 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____11169)::[] -> wp1
              | uu____11182 ->
                  let uu____11188 =
                    let uu____11189 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____11189
                     in
                  failwith uu____11188
               in
            let uu____11192 =
              let uu____11198 =
                let uu____11199 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____11199  in
              [uu____11198]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____11192;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____11200 = lift_c1 ()  in solve_eq uu____11200 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___128_11204  ->
                       match uu___128_11204 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____11205 -> false))
                in
             let uu____11206 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____11230)::uu____11231,(wp2,uu____11233)::uu____11234)
                   -> (wp1, wp2)
               | uu____11275 ->
                   let uu____11288 =
                     let uu____11289 =
                       FStar_Syntax_Print.lid_to_string
                         c11.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____11290 =
                       FStar_Syntax_Print.lid_to_string
                         c21.FStar_Syntax_Syntax.effect_name
                        in
                     FStar_Util.format2
                       "Got effects %s and %s, expected normalized effects"
                       uu____11289 uu____11290
                      in
                   failwith uu____11288
                in
             match uu____11206 with
             | (wpc1,wpc2) ->
                 let uu____11307 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____11307
                 then
                   let uu____11310 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type"
                      in
                   solve_t env uu____11310 wl
                 else
                   (let c2_decl =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____11315 =
                      FStar_All.pipe_right
                        c2_decl.FStar_Syntax_Syntax.qualifiers
                        (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
                       in
                    if uu____11315
                    then
                      let c1_repr =
                        let uu____11318 =
                          let uu____11319 =
                            let uu____11320 = lift_c1 ()  in
                            FStar_Syntax_Syntax.mk_Comp uu____11320  in
                          let uu____11321 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c11.FStar_Syntax_Syntax.result_typ
                             in
                          FStar_TypeChecker_Env.reify_comp env uu____11319
                            uu____11321
                           in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11318
                         in
                      let c2_repr =
                        let uu____11323 =
                          let uu____11324 = FStar_Syntax_Syntax.mk_Comp c21
                             in
                          let uu____11325 =
                            env.FStar_TypeChecker_Env.universe_of env
                              c21.FStar_Syntax_Syntax.result_typ
                             in
                          FStar_TypeChecker_Env.reify_comp env uu____11324
                            uu____11325
                           in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.UnfoldUntil
                             FStar_Syntax_Syntax.Delta_constant;
                          FStar_TypeChecker_Normalize.WHNF] env uu____11323
                         in
                      let prob =
                        let uu____11327 =
                          let uu____11330 =
                            let uu____11331 =
                              FStar_Syntax_Print.term_to_string c1_repr  in
                            let uu____11332 =
                              FStar_Syntax_Print.term_to_string c2_repr  in
                            FStar_Util.format2 "sub effect repr: %s <: %s"
                              uu____11331 uu____11332
                             in
                          sub_prob c1_repr
                            problem.FStar_TypeChecker_Common.relation c2_repr
                            uu____11330
                           in
                        FStar_TypeChecker_Common.TProb uu____11327  in
                      let wl1 =
                        let uu____11334 =
                          let uu____11336 =
                            FStar_All.pipe_right (p_guard prob) Prims.fst  in
                          Some uu____11336  in
                        solve_prob orig uu____11334 [] wl  in
                      solve env (attempt [prob] wl1)
                    else
                      (let g =
                         if env.FStar_TypeChecker_Env.lax
                         then FStar_Syntax_Util.t_true
                         else
                           if is_null_wp_2
                           then
                             ((let uu____11343 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel")
                                  in
                               if uu____11343
                               then
                                 FStar_Util.print_string
                                   "Using trivial wp ... \n"
                               else ());
                              (let uu____11345 =
                                 let uu____11348 =
                                   let uu____11349 =
                                     let uu____11359 =
                                       let uu____11360 =
                                         let uu____11361 =
                                           env.FStar_TypeChecker_Env.universe_of
                                             env
                                             c11.FStar_Syntax_Syntax.result_typ
                                            in
                                         [uu____11361]  in
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         uu____11360 env c2_decl
                                         c2_decl.FStar_Syntax_Syntax.trivial
                                        in
                                     let uu____11362 =
                                       let uu____11364 =
                                         FStar_Syntax_Syntax.as_arg
                                           c11.FStar_Syntax_Syntax.result_typ
                                          in
                                       let uu____11365 =
                                         let uu____11367 =
                                           let uu____11368 =
                                             (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                               c11.FStar_Syntax_Syntax.result_typ
                                               wpc1
                                              in
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             uu____11368
                                            in
                                         [uu____11367]  in
                                       uu____11364 :: uu____11365  in
                                     (uu____11359, uu____11362)  in
                                   FStar_Syntax_Syntax.Tm_app uu____11349  in
                                 FStar_Syntax_Syntax.mk uu____11348  in
                               uu____11345
                                 (Some
                                    (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                 r))
                           else
                             (let uu____11379 =
                                let uu____11382 =
                                  let uu____11383 =
                                    let uu____11393 =
                                      let uu____11394 =
                                        let uu____11395 =
                                          env.FStar_TypeChecker_Env.universe_of
                                            env
                                            c21.FStar_Syntax_Syntax.result_typ
                                           in
                                        [uu____11395]  in
                                      FStar_TypeChecker_Env.inst_effect_fun_with
                                        uu____11394 env c2_decl
                                        c2_decl.FStar_Syntax_Syntax.stronger
                                       in
                                    let uu____11396 =
                                      let uu____11398 =
                                        FStar_Syntax_Syntax.as_arg
                                          c21.FStar_Syntax_Syntax.result_typ
                                         in
                                      let uu____11399 =
                                        let uu____11401 =
                                          FStar_Syntax_Syntax.as_arg wpc2  in
                                        let uu____11402 =
                                          let uu____11404 =
                                            let uu____11405 =
                                              (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                c11.FStar_Syntax_Syntax.result_typ
                                                wpc1
                                               in
                                            FStar_All.pipe_left
                                              FStar_Syntax_Syntax.as_arg
                                              uu____11405
                                             in
                                          [uu____11404]  in
                                        uu____11401 :: uu____11402  in
                                      uu____11398 :: uu____11399  in
                                    (uu____11393, uu____11396)  in
                                  FStar_Syntax_Syntax.Tm_app uu____11383  in
                                FStar_Syntax_Syntax.mk uu____11382  in
                              uu____11379
                                (Some
                                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                r)
                          in
                       let base_prob =
                         let uu____11416 =
                           sub_prob c11.FStar_Syntax_Syntax.result_typ
                             problem.FStar_TypeChecker_Common.relation
                             c21.FStar_Syntax_Syntax.result_typ "result type"
                            in
                         FStar_All.pipe_left
                           (fun _0_66  ->
                              FStar_TypeChecker_Common.TProb _0_66)
                           uu____11416
                          in
                       let wl1 =
                         let uu____11422 =
                           let uu____11424 =
                             let uu____11427 =
                               FStar_All.pipe_right (p_guard base_prob)
                                 Prims.fst
                                in
                             FStar_Syntax_Util.mk_conj uu____11427 g  in
                           FStar_All.pipe_left (fun _0_67  -> Some _0_67)
                             uu____11424
                            in
                         solve_prob orig uu____11422 [] wl  in
                       solve env (attempt [base_prob] wl1))))
           in
        let uu____11437 = FStar_Util.physical_equality c1 c2  in
        if uu____11437
        then
          let uu____11438 = solve_prob orig None [] wl  in
          solve env uu____11438
        else
          ((let uu____11441 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____11441
            then
              let uu____11442 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____11443 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____11442
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____11443
            else ());
           (let uu____11445 =
              let uu____11448 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____11449 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____11448, uu____11449)  in
            match uu____11445 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____11453),FStar_Syntax_Syntax.Total
                    (t2,uu____11455)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____11468 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11468 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____11471,FStar_Syntax_Syntax.Total uu____11472) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let uu____11521 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____11521 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let uu____11528 =
                       let uu___167_11531 = problem  in
                       let uu____11534 =
                         let uu____11535 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11535
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___167_11531.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____11534;
                         FStar_TypeChecker_Common.relation =
                           (uu___167_11531.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___167_11531.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___167_11531.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___167_11531.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___167_11531.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___167_11531.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___167_11531.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___167_11531.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11528 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let uu____11540 =
                       let uu___168_11543 = problem  in
                       let uu____11546 =
                         let uu____11547 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____11547
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___168_11543.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___168_11543.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___168_11543.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____11546;
                         FStar_TypeChecker_Common.element =
                           (uu___168_11543.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___168_11543.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___168_11543.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___168_11543.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___168_11543.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___168_11543.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____11540 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____11548,FStar_Syntax_Syntax.Comp uu____11549) ->
                     let uu____11550 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____11550
                     then
                       let uu____11551 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type"
                          in
                       solve_t env uu____11551 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            &&
                            (FStar_Ident.lid_equals
                               c1_comp.FStar_Syntax_Syntax.effect_name
                               c2_comp.FStar_Syntax_Syntax.effect_name)
                        then solve_eq c1_comp c2_comp
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____11561 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____11561
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____11563 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____11563 with
                            | None  ->
                                let uu____11565 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____11566 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____11566)
                                   in
                                if uu____11565
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (c12.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (c22.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mlift =
                                        FStar_TypeChecker_Env.identity_mlift
                                    }  in
                                  solve_sub c12 edge c22
                                else
                                  (let uu____11569 =
                                     let uu____11570 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____11571 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____11570 uu____11571
                                      in
                                   giveup env uu____11569 orig)
                            | Some edge -> solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11576 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____11596  ->
              match uu____11596 with
              | (uu____11607,uu____11608,u,uu____11610,uu____11611,uu____11612)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____11576 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11641 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____11641 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____11651 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____11663  ->
                match uu____11663 with
                | (u1,u2) ->
                    let uu____11668 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____11669 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____11668 uu____11669))
         in
      FStar_All.pipe_right uu____11651 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____11681,[])) -> "{}"
      | uu____11694 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____11704 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____11704
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____11707 =
              FStar_List.map
                (fun uu____11711  ->
                   match uu____11711 with
                   | (uu____11714,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____11707 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____11718 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____11718 imps
  
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
        FStar_TypeChecker_Env.univ_ineqs = uu____11738;
        FStar_TypeChecker_Env.implicits = uu____11739;_} -> true
    | uu____11753 -> false
  
let trivial_guard : FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let abstract_guard :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t Prims.option ->
      FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun x  ->
    fun g  ->
      match g with
      | None |Some
        { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
          FStar_TypeChecker_Env.deferred = _;
          FStar_TypeChecker_Env.univ_ineqs = _;
          FStar_TypeChecker_Env.implicits = _;_} -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____11780 -> failwith "impossible"  in
          let uu____11781 =
            let uu___169_11782 = g1  in
            let uu____11783 =
              let uu____11784 =
                let uu____11785 =
                  let uu____11789 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____11789]  in
                let uu____11790 =
                  let uu____11797 =
                    let uu____11803 =
                      let uu____11804 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                         in
                      FStar_All.pipe_right uu____11804
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    FStar_All.pipe_right uu____11803
                      (fun _0_68  -> FStar_Util.Inl _0_68)
                     in
                  Some uu____11797  in
                FStar_Syntax_Util.abs uu____11785 f uu____11790  in
              FStar_All.pipe_left
                (fun _0_69  -> FStar_TypeChecker_Common.NonTrivial _0_69)
                uu____11784
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____11783;
              FStar_TypeChecker_Env.deferred =
                (uu___169_11782.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___169_11782.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___169_11782.FStar_TypeChecker_Env.implicits)
            }  in
          Some uu____11781
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___170_11825 = g  in
          let uu____11826 =
            let uu____11827 =
              let uu____11828 =
                let uu____11831 =
                  let uu____11832 =
                    let uu____11842 =
                      let uu____11844 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____11844]  in
                    (f, uu____11842)  in
                  FStar_Syntax_Syntax.Tm_app uu____11832  in
                FStar_Syntax_Syntax.mk uu____11831  in
              uu____11828
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_70  -> FStar_TypeChecker_Common.NonTrivial _0_70)
              uu____11827
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____11826;
            FStar_TypeChecker_Env.deferred =
              (uu___170_11825.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___170_11825.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___170_11825.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____11857 ->
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
          let uu____11867 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____11867
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____11876 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____11907 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____11907;
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
          let uu___171_11945 = g  in
          let uu____11946 =
            let uu____11947 = FStar_Syntax_Util.close_forall binders f  in
            FStar_All.pipe_right uu____11947
              (fun _0_71  -> FStar_TypeChecker_Common.NonTrivial _0_71)
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____11946;
            FStar_TypeChecker_Env.deferred =
              (uu___171_11945.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___171_11945.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___171_11945.FStar_TypeChecker_Env.implicits)
          }
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____11985 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____11985
    then
      let uu____11986 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____11987 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____11986
        (rel_to_string rel) uu____11987
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
            let uu____12007 =
              let uu____12009 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_72  -> Some _0_72) uu____12009  in
            FStar_Syntax_Syntax.new_bv uu____12007 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____12015 =
              let uu____12017 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_73  -> Some _0_73) uu____12017  in
            let uu____12019 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____12015 uu____12019  in
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
          let uu____12042 = FStar_Options.eager_inference ()  in
          if uu____12042
          then
            let uu___172_12043 = probs  in
            {
              attempting = (uu___172_12043.attempting);
              wl_deferred = (uu___172_12043.wl_deferred);
              ctr = (uu___172_12043.ctr);
              defer_ok = false;
              smt_ok = (uu___172_12043.smt_ok);
              tcenv = (uu___172_12043.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12054 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____12054
              then
                let uu____12055 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____12055
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
          ((let uu____12065 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____12065
            then
              let uu____12066 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____12066
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____12070 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____12070
             then
               let uu____12071 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____12071
             else ());
            (let f2 =
               let uu____12074 =
                 let uu____12075 = FStar_Syntax_Util.unmeta f1  in
                 uu____12075.FStar_Syntax_Syntax.n  in
               match uu____12074 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____12079 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___173_12080 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___173_12080.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___173_12080.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___173_12080.FStar_TypeChecker_Env.implicits)
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
            let uu____12095 =
              let uu____12096 =
                let uu____12097 =
                  let uu____12098 =
                    FStar_All.pipe_right (p_guard prob) Prims.fst  in
                  FStar_All.pipe_right uu____12098
                    (fun _0_74  -> FStar_TypeChecker_Common.NonTrivial _0_74)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12097;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____12096  in
            FStar_All.pipe_left (fun _0_75  -> Some _0_75) uu____12095
  
let try_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____12122 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____12122
         then
           let uu____12123 = FStar_Syntax_Print.term_to_string t1  in
           let uu____12124 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "try_teq of %s and %s\n" uu____12123 uu____12124
         else ());
        (let prob =
           let uu____12127 =
             let uu____12130 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
               uu____12130
              in
           FStar_All.pipe_left
             (fun _0_76  -> FStar_TypeChecker_Common.TProb _0_76) uu____12127
            in
         let g =
           let uu____12135 =
             let uu____12137 = singleton env prob  in
             solve_and_commit env uu____12137 (fun uu____12138  -> None)  in
           FStar_All.pipe_left (with_guard env prob) uu____12135  in
         g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12152 = try_teq env t1 t2  in
        match uu____12152 with
        | None  ->
            let uu____12154 =
              let uu____12155 =
                let uu____12158 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____12159 = FStar_TypeChecker_Env.get_range env  in
                (uu____12158, uu____12159)  in
              FStar_Errors.Error uu____12155  in
            Prims.raise uu____12154
        | Some g ->
            ((let uu____12162 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12162
              then
                let uu____12163 = FStar_Syntax_Print.term_to_string t1  in
                let uu____12164 = FStar_Syntax_Print.term_to_string t2  in
                let uu____12165 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____12163
                  uu____12164 uu____12165
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
          (let uu____12181 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____12181
           then
             let uu____12182 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____12183 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____12182
               uu____12183
           else ());
          (let uu____12185 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____12185 with
           | (prob,x) ->
               let g =
                 let uu____12193 =
                   let uu____12195 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____12195
                     (fun uu____12196  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____12193  in
               ((let uu____12202 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____12202
                 then
                   let uu____12203 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____12204 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____12205 =
                     let uu____12206 = FStar_Util.must g  in
                     guard_to_string env uu____12206  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____12203 uu____12204 uu____12205
                 else ());
                abstract_guard x g))
  
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
          let uu____12230 = FStar_TypeChecker_Env.get_range env  in
          let uu____12231 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.report uu____12230 uu____12231
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12243 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____12243
         then
           let uu____12244 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____12245 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____12244
             uu____12245
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____12250 =
             let uu____12253 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____12253 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_77  -> FStar_TypeChecker_Common.CProb _0_77) uu____12250
            in
         let uu____12256 =
           let uu____12258 = singleton env prob  in
           solve_and_commit env uu____12258 (fun uu____12259  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____12256)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12278  ->
        match uu____12278 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____12303 =
                 let uu____12304 =
                   let uu____12307 =
                     let uu____12308 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____12309 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____12308 uu____12309
                      in
                   let uu____12310 = FStar_TypeChecker_Env.get_range env  in
                   (uu____12307, uu____12310)  in
                 FStar_Errors.Error uu____12304  in
               Prims.raise uu____12303)
               in
            let equiv v1 v' =
              let uu____12318 =
                let uu____12321 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____12322 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____12321, uu____12322)  in
              match uu____12318 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____12330 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____12344 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____12344 with
                      | FStar_Syntax_Syntax.U_unif uu____12348 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12359  ->
                                    match uu____12359 with
                                    | (u,v') ->
                                        let uu____12365 = equiv v1 v'  in
                                        if uu____12365
                                        then
                                          let uu____12367 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____12367 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____12377 -> []))
               in
            let uu____12380 =
              let wl =
                let uu___174_12383 = empty_worklist env  in
                {
                  attempting = (uu___174_12383.attempting);
                  wl_deferred = (uu___174_12383.wl_deferred);
                  ctr = (uu___174_12383.ctr);
                  defer_ok = false;
                  smt_ok = (uu___174_12383.smt_ok);
                  tcenv = (uu___174_12383.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____12390  ->
                      match uu____12390 with
                      | (lb,v1) ->
                          let uu____12395 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____12395 with
                           | USolved wl1 -> ()
                           | uu____12397 -> fail lb v1)))
               in
            let rec check_ineq uu____12403 =
              match uu____12403 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____12410) -> true
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
                   | (FStar_Syntax_Syntax.U_max us,uu____12426) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12430,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____12435 -> false)
               in
            let uu____12438 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____12444  ->
                      match uu____12444 with
                      | (u,v1) ->
                          let uu____12449 = check_ineq (u, v1)  in
                          if uu____12449
                          then true
                          else
                            ((let uu____12452 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____12452
                              then
                                let uu____12453 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____12454 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____12453
                                  uu____12454
                              else ());
                             false)))
               in
            if uu____12438
            then ()
            else
              ((let uu____12458 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____12458
                then
                  ((let uu____12460 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____12460);
                   FStar_Unionfind.rollback tx;
                   (let uu____12466 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____12466))
                else ());
               (let uu____12472 =
                  let uu____12473 =
                    let uu____12476 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____12476)
                     in
                  FStar_Errors.Error uu____12473  in
                Prims.raise uu____12472))
  
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
      let fail uu____12509 =
        match uu____12509 with
        | (d,s) ->
            let msg = explain env d s  in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____12519 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____12519
       then
         let uu____12520 = wl_to_string wl  in
         let uu____12521 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____12520 uu____12521
       else ());
      (let g1 =
         let uu____12533 = solve_and_commit env wl fail  in
         match uu____12533 with
         | Some [] ->
             let uu___175_12540 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___175_12540.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___175_12540.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___175_12540.FStar_TypeChecker_Env.implicits)
             }
         | uu____12543 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___176_12546 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___176_12546.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___176_12546.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___176_12546.FStar_TypeChecker_Env.implicits)
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
            let uu___177_12572 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___177_12572.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___177_12572.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___177_12572.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____12573 =
            let uu____12574 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____12574  in
          if uu____12573
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____12580 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm")
                      in
                   if uu____12580
                   then
                     let uu____12581 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____12582 =
                       let uu____12583 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____12583
                        in
                     FStar_Errors.diag uu____12581 uu____12582
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
                         ((let uu____12592 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____12592
                           then
                             let uu____12593 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____12594 =
                               let uu____12595 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____12595
                                in
                             FStar_Errors.diag uu____12593 uu____12594
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
      let uu____12603 = discharge_guard' None env g true  in
      match uu____12603 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____12623 = FStar_Unionfind.find u  in
      match uu____12623 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____12632 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____12647 = acc  in
      match uu____12647 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____12693 = hd1  in
               (match uu____12693 with
                | (uu____12700,env,u,tm,k,r) ->
                    let uu____12706 = unresolved u  in
                    if uu____12706
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____12724 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____12724
                        then
                          let uu____12725 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____12729 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____12730 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____12725 uu____12729 uu____12730
                        else ());
                       (let uu____12732 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___178_12736 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___178_12736.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___178_12736.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___178_12736.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___178_12736.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___178_12736.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___178_12736.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___178_12736.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___178_12736.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___178_12736.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___178_12736.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___178_12736.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___178_12736.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___178_12736.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___178_12736.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___178_12736.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___178_12736.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___178_12736.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___178_12736.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___178_12736.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___178_12736.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___178_12736.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___178_12736.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___178_12736.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____12732 with
                        | (uu____12737,uu____12738,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___179_12741 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___179_12741.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___179_12741.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___179_12741.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____12744 =
                                discharge_guard'
                                  (Some
                                     (fun uu____12748  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____12744 with
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
    let uu___180_12763 = g  in
    let uu____12764 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___180_12763.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___180_12763.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___180_12763.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12764
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____12792 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____12792 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____12799 = discharge_guard env g1  in
          FStar_All.pipe_left Prims.ignore uu____12799
      | (reason,uu____12801,uu____12802,e,t,r)::uu____12806 ->
          let uu____12820 =
            let uu____12821 = FStar_Syntax_Print.term_to_string t  in
            let uu____12822 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____12821 uu____12822 reason
             in
          FStar_Errors.report r uu____12820
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___181_12829 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___181_12829.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___181_12829.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___181_12829.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____12847 = try_teq env t1 t2  in
        match uu____12847 with
        | None  -> false
        | Some g ->
            let uu____12850 = discharge_guard' None env g false  in
            (match uu____12850 with
             | Some uu____12854 -> true
             | None  -> false)
  