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
            (uv, uv)
        | uu____45 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let _0_237 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders _0_237  in
            let uv =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r
               in
            let _0_238 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (_0_238, uv)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____118 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____144 -> false
  
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
    match projectee with | Success _0 -> true | uu____224 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____238 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____255 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____259 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____263 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___99_274  ->
    match uu___99_274 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____287 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
  match uu____287 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t) ->
      let _0_240 = FStar_Syntax_Print.uvar_to_string u  in
      let _0_239 = FStar_Syntax_Print.term_to_string t  in
      FStar_Util.format2 "(%s:%s)" _0_240 _0_239
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____618;
         FStar_Syntax_Syntax.pos = uu____619;
         FStar_Syntax_Syntax.vars = uu____620;_},args)
      ->
      let _0_243 = FStar_Syntax_Print.uvar_to_string u  in
      let _0_242 = FStar_Syntax_Print.term_to_string ty  in
      let _0_241 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" _0_243 _0_242 _0_241
  | uu____340 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___103_660  ->
      match uu___103_660 with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_258 =
            let _0_257 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let _0_256 =
              let _0_255 = term_to_string env p.FStar_TypeChecker_Common.lhs
                 in
              let _0_254 =
                let _0_253 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let _0_252 =
                  let _0_251 =
                    let _0_250 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let _0_249 =
                      let _0_248 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let _0_247 =
                        let _0_246 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let _0_245 =
                          let _0_244 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [_0_244]  in
                        _0_246 :: _0_245  in
                      _0_248 :: _0_247  in
                    _0_250 :: _0_249  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    _0_251
                   in
                _0_253 :: _0_252  in
              _0_255 :: _0_254  in
            _0_257 :: _0_256  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____664
      | FStar_TypeChecker_Common.CProb p ->
          let uu____691 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let _0_259 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _0_260
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_259
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___104_698  ->
      match uu___104_698 with
      | UNIV (u,t) ->
          let x =
            let uu____363 = FStar_Options.hide_uvar_nums ()  in
            match uu____363 with
            | true  -> "?"
            | uu____364 ->
                let _0_261 = FStar_Unionfind.uvar_id u  in
                FStar_All.pipe_right _0_261 FStar_Util.string_of_int
             in
          let _0_262 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x _0_262
      | TERM ((u,uu____367),t) ->
          let x =
            let uu____372 = FStar_Options.hide_uvar_nums ()  in
            match uu____372 with
            | true  -> "?"
            | uu____373 ->
                let _0_263 = FStar_Unionfind.uvar_id u  in
                FStar_All.pipe_right _0_263 FStar_Util.string_of_int
             in
          let _0_264 = FStar_TypeChecker_Normalize.term_to_string env t  in
          FStar_Util.format2 "TERM %s %s" x _0_264
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let _0_265 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right _0_265 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let _0_267 =
      let _0_266 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right _0_266
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right _0_267 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____756 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____414  ->
            match uu____414 with
            | (x,uu____418) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right _0_268 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let _0_269 = Prims.op_Negation (FStar_Options.eager_inference ())  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____773;
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
        let uu___127_434 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___135_787.wl_deferred);
          ctr = (uu___135_787.ctr);
          defer_ok = (uu___135_787.defer_ok);
          smt_ok;
          tcenv = (uu___135_787.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___128_459 = empty_worklist env  in
  let _0_270 = FStar_List.map Prims.snd g  in
  {
    attempting = uu____813;
    wl_deferred = (uu___136_812.wl_deferred);
    ctr = (uu___136_812.ctr);
    defer_ok = false;
    smt_ok = (uu___128_459.smt_ok);
    tcenv = (uu___128_459.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___129_471 = wl  in
        {
          attempting = (uu___137_825.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___137_825.ctr);
          defer_ok = (uu___137_825.defer_ok);
          smt_ok = (uu___137_825.smt_ok);
          tcenv = (uu___137_825.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___130_483 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___138_837.wl_deferred);
        ctr = (uu___138_837.ctr);
        defer_ok = (uu___138_837.defer_ok);
        smt_ok = (uu___138_837.smt_ok);
        tcenv = (uu___138_837.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____848 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         match uu____494 with
         | true  ->
             let _0_271 = prob_to_string env prob  in
             FStar_Util.print2 "Failed %s:\n%s\n" reason _0_271
         | uu____495 -> ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___105_853  ->
    match uu___105_853 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___131_514 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___139_869.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___139_869.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___139_869.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___139_869.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___139_869.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___139_869.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___131_514.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  match p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  with
  | true  -> invert p
  | uu____532 -> p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___106_890  ->
    match uu___106_890 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_31  -> FStar_TypeChecker_Common.TProb _0_31)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_273  -> FStar_TypeChecker_Common.CProb _0_273)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___107_906  ->
      match uu___107_906 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___105_554  ->
    match uu___105_554 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___106_563  ->
    match uu___106_563 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___107_573  ->
    match uu___107_573 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___108_583  ->
    match uu___108_583 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___112_949  ->
    match uu___112_949 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___110_605  ->
    match uu___110_605 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___114_969  ->
    match uu___114_969 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_33  -> FStar_TypeChecker_Common.TProb _0_33) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_275  -> FStar_TypeChecker_Common.CProb _0_275) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let _0_276 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    _0_276 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____636  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let _0_278 = next_pid ()  in
  let _0_277 = new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0
     in
  {
    FStar_TypeChecker_Common.pid = uu____1044;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1045;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let _0_280 = next_pid ()  in
  let _0_279 = new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0
     in
  {
    FStar_TypeChecker_Common.pid = uu____1092;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1093;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let _0_281 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1134;
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
        let uu____1186 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        match uu____813 with
        | true  ->
            let _0_284 =
              FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
            let _0_283 = prob_to_string env d  in
            let _0_282 =
              FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
               in
            FStar_Util.format4
              "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
              _0_284 _0_283 _0_282 s
        | uu____815 ->
            let d = maybe_invert_p d  in
            let rel =
              match p_rel d with
              | FStar_TypeChecker_Common.EQ  -> "equal to"
              | FStar_TypeChecker_Common.SUB  -> "a subtype of"
              | uu____818 -> failwith "impossible"  in
            let uu____819 =
              match d with
              | FStar_TypeChecker_Common.TProb tp ->
                  let _0_286 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      tp.FStar_TypeChecker_Common.lhs
                     in
                  let _0_285 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      tp.FStar_TypeChecker_Common.rhs
                     in
                  (_0_286, _0_285)
              | FStar_TypeChecker_Common.CProb cp ->
                  let _0_288 =
                    FStar_TypeChecker_Normalize.comp_to_string env
                      cp.FStar_TypeChecker_Common.lhs
                     in
                  let _0_287 =
                    FStar_TypeChecker_Normalize.comp_to_string env
                      cp.FStar_TypeChecker_Common.rhs
                     in
                  (_0_288, _0_287)
               in
            (match uu____819 with
             | (lhs,rhs) ->
                 FStar_Util.format3 "%s is not %s the expected type %s" lhs
                   rel rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___115_1218  ->
            match uu___115_1218 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____845 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____848),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___113_871  ->
           match uu___113_871 with
           | UNIV uu____873 -> None
           | TERM ((u,uu____877),t) ->
               let uu____881 = FStar_Unionfind.equivalent uv u  in
               (match uu____881 with | true  -> Some t | uu____886 -> None))
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___117_1280  ->
           match uu___117_1280 with
           | UNIV (u',t) ->
               let uu____904 = FStar_Unionfind.equivalent u u'  in
               (match uu____904 with | true  -> Some t | uu____907 -> None)
           | uu____908 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      FStar_Syntax_Subst.compress
        (let _0_289 = FStar_Syntax_Util.unmeta t  in
         FStar_TypeChecker_Normalize.normalize
           [FStar_TypeChecker_Normalize.Beta;
           FStar_TypeChecker_Normalize.WHNF] env _0_289)
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      FStar_Syntax_Subst.compress
        (FStar_TypeChecker_Normalize.normalize
           [FStar_TypeChecker_Normalize.Beta] env t)
  
let norm_arg env t =
  let _0_290 = sn env (Prims.fst t)  in (_0_290, (Prims.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1339  ->
              match uu____1339 with
              | (x,imp) ->
                  let _0_292 =
                    let uu___132_962 = x  in
                    let _0_291 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___140_1347.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___132_962.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = _0_291
                    }  in
                  (_0_292, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u  in
        match u with
        | FStar_Syntax_Syntax.U_succ u -> FStar_Syntax_Syntax.U_succ (aux u)
        | FStar_Syntax_Syntax.U_max us ->
            FStar_Syntax_Syntax.U_max (FStar_List.map aux us)
        | uu____977 -> u  in
      let _0_293 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _0_293
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        (match norm with
         | true  -> ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
         | uu____1083 ->
             let uu____1084 =
               normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
                 t1
                in
             (match uu____1084 with
              | {
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                    (x,phi);
                  FStar_Syntax_Syntax.tk = uu____1096;
                  FStar_Syntax_Syntax.pos = uu____1097;
                  FStar_Syntax_Syntax.vars = uu____1098;_} ->
                  ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
              | tt ->
                  failwith
                    (let _0_295 = FStar_Syntax_Print.term_to_string tt  in
                     let _0_294 = FStar_Syntax_Print.tag_of_term tt  in
                     FStar_Util.format2 "impossible: Got %s ... %s\n" _0_295
                       _0_294)))
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        (match norm with
         | true  -> (t1, None)
         | uu____1151 ->
             let t1' =
               normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
                 t1
                in
             let uu____1153 =
               (FStar_Syntax_Subst.compress t1').FStar_Syntax_Syntax.n  in
             (match uu____1153 with
              | FStar_Syntax_Syntax.Tm_refine uu____1163 -> aux true t1'
              | uu____1168 -> (t1, None)))
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
        failwith
          (let _0_297 = FStar_Syntax_Print.term_to_string t1  in
           let _0_296 = FStar_Syntax_Print.tag_of_term t1  in
           FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _0_297
             _0_296)
     in
  let _0_298 = whnf env t1  in aux false _0_298 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let _0_300 =
        let _0_299 = empty_worklist env  in base_and_refinement env _0_299 t
         in
      FStar_All.pipe_right _0_300 Prims.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let _0_301 = FStar_Syntax_Syntax.null_bv t  in
    (_0_301, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____1260 = base_and_refinement env wl t  in
  match uu____1260 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____1319 =
  match uu____1319 with
  | (t_base,refopt) ->
      let uu____1749 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____1333 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___118_1773  ->
      match uu___118_1773 with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_304 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let _0_303 =
            FStar_Syntax_Print.term_to_string
              (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
             in
          let _0_302 =
            FStar_Syntax_Print.term_to_string
              (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" _0_304 _0_303
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_302
      | FStar_TypeChecker_Common.CProb p ->
          let _0_307 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let _0_306 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let _0_305 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" _0_307 _0_306
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_305
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____1791 =
      let uu____1793 =
        let uu____1795 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1376  ->
                  match uu____1376 with | (uu____1380,uu____1381,x) -> x))
           in
        FStar_List.append wl.attempting _0_308  in
      FStar_List.map (wl_prob_to_string wl) _0_309  in
    FStar_All.pipe_right _0_310 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1398 =
          let uu____1408 =
            (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n  in
          match uu____1408 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              (match (FStar_List.length bs) = (FStar_List.length ys) with
               | true  ->
                   let _0_311 = FStar_Syntax_Subst.open_comp bs c  in
                   ((ys, t), _0_311)
               | uu____1457 ->
                   let uu____1458 = FStar_Syntax_Util.abs_formals t  in
                   (match uu____1458 with
                    | (ys',t,uu____1479) ->
                        let _0_312 = FStar_Syntax_Util.arrow_formals_comp k
                           in
                        (((FStar_List.append ys ys'), t), _0_312)))
          | uu____1507 ->
              let _0_314 =
                let _0_313 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_313)
                 in
              ((ys, t), _0_314)
           in
        match uu____1398 with
        | ((ys,t),(xs,c)) ->
            (match (FStar_List.length xs) <> (FStar_List.length ys) with
             | true  ->
                 FStar_Syntax_Util.abs ys t
                   (Some
                      (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
             | uu____1560 ->
                 let c =
                   let _0_315 = FStar_Syntax_Util.rename_binders xs ys  in
                   FStar_Syntax_Subst.subst_comp _0_315 c  in
                 let _0_319 =
                   let _0_318 =
                     FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c)
                       (fun _0_316  -> FStar_Util.Inl _0_316)
                      in
                   FStar_All.pipe_right _0_318 (fun _0_317  -> Some _0_317)
                    in
                 FStar_Syntax_Util.abs ys t _0_319)
  
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
            let uu____1607 = p_guard prob  in
            match uu____1607 with
            | (uu____1610,uv) ->
                ((let uu____1613 =
                    (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
                     in
                  match uu____1613 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi = u_abs k bs phi  in
                      ((let uu____1631 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        match uu____1631 with
                        | true  ->
                            let _0_322 =
                              FStar_Util.string_of_int (p_pid prob)  in
                            let _0_321 = FStar_Syntax_Print.term_to_string uv
                               in
                            let _0_320 =
                              FStar_Syntax_Print.term_to_string phi  in
                            FStar_Util.print3
                              "Solving %s (%s) with formula %s\n" _0_322
                              _0_321 _0_320
                        | uu____1632 -> ());
                       FStar_Syntax_Util.set_uvar uvar phi)
                  | uu____1635 ->
                      (match Prims.op_Negation resolve_ok with
                       | true  ->
                           failwith
                             "Impossible: this instance has already been assigned a solution"
                       | uu____1636 -> ()));
                 commit uvis;
                 (let uu___133_1638 = wl  in
                  {
                    attempting = (uu___141_2108.attempting);
                    wl_deferred = (uu___141_2108.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___141_2108.defer_ok);
                    smt_ok = (uu___141_2108.smt_ok);
                    tcenv = (uu___141_2108.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2121 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         match uu____1651 with
         | true  ->
             let _0_325 = FStar_Util.string_of_int pid  in
             let _0_324 =
               let _0_323 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
               FStar_All.pipe_right _0_323 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" _0_325 _0_324
         | uu____1653 -> ());
        commit sol;
        (let uu___134_1655 = wl  in
         {
           attempting = (uu___142_2129.attempting);
           wl_deferred = (uu___142_2129.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___142_2129.defer_ok);
           smt_ok = (uu___142_2129.smt_ok);
           tcenv = (uu___142_2129.tcenv)
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
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2158,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t,FStar_TypeChecker_Common.NonTrivial f) ->
                Some (FStar_Syntax_Util.mk_conj t f)
             in
          (let uu____1695 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           match uu____1695 with
           | true  ->
               let _0_328 =
                 FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)
                  in
               let _0_327 =
                 let _0_326 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                    in
                 FStar_All.pipe_right _0_326 (FStar_String.concat ", ")  in
               FStar_Util.print2 "Solving %s: with %s\n" _0_328 _0_327
           | uu____1697 -> ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let _0_330 =
    let _0_329 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right _0_329 FStar_Util.set_elements  in
  FStar_All.pipe_right _0_330
    (FStar_Util.for_some
       (fun uu____1736  ->
          match uu____1736 with
          | (uv,uu____1744) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok = Prims.op_Negation (occurs wl uk t)  in
  let msg =
    match occurs_ok with
    | true  -> None
    | uu____1791 ->
        Some
          (let _0_332 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk)  in
           let _0_331 = FStar_Syntax_Print.term_to_string t  in
           FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _0_332
             _0_331)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____1842 = occurs_check env wl uk t  in
  match uu____1842 with
  | (occurs_ok,msg) ->
      let _0_333 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, _0_333, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set v1  in
  let uu____1922 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2440  ->
            fun uu____2441  ->
              match (uu____2440, uu____2441) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____1990 =
                    let _0_334 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation _0_334  in
                  (match uu____1990 with
                   | true  -> (isect, isect_set)
                   | uu____2001 ->
                       let fvs =
                         FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort
                          in
                       let uu____2004 =
                         FStar_Util.set_is_subset_of fvs isect_set  in
                       (match uu____2004 with
                        | true  ->
                            let _0_335 = FStar_Util.set_add x isect_set  in
                            (((x, imp) :: isect), _0_335)
                        | uu____2017 -> (isect, isect_set))))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____1922 with | (isect,uu____2031) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2577  ->
          fun uu____2578  ->
            match (uu____2577, uu____2578) with
            | ((a,uu____2588),(b,uu____2590)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd = norm_arg env arg  in
  match (Prims.fst hd).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2634 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2143  ->
                match uu____2143 with
                | (b,uu____2147) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      (match uu____2137 with
       | true  -> None
       | uu____2153 -> Some (a, (Prims.snd hd)))
  | uu____2156 -> None 
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
        | hd::rest ->
            let uu____2199 = pat_var_opt env seen hd  in
            (match uu____2199 with
             | None  ->
                 ((let uu____2704 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   match uu____2207 with
                   | true  ->
                       let _0_336 =
                         FStar_All.pipe_left
                           FStar_Syntax_Print.term_to_string (Prims.fst hd)
                          in
                       FStar_Util.print1 "Not a pattern: %s\n" _0_336
                   | uu____2208 -> ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2219 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
       in
    match uu____2219 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2233 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2796;
         FStar_Syntax_Syntax.pos = uu____2797;
         FStar_Syntax_Syntax.vars = uu____2798;_},args)
      -> (t, uv, k, args)
  | uu____2338 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____2392 = destruct_flex_t t  in
  match uu____2392 with
  | (t,uv,k,args) ->
      let uu____2460 = pat_vars env [] args  in
      (match uu____2460 with
       | Some vars -> ((t, uv, k, args), (Some vars))
       | uu____2516 -> ((t, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option *
  FStar_Syntax_Syntax.delta_depth Prims.option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____2564 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option *
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____2587 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____2591 -> false
  
let head_match : match_result -> match_result =
  fun uu___116_2594  ->
    match uu___116_2594 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____2603 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3117 ->
          let uu____3118 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____3118 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3128 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth Prims.option
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t  in
      match t.FStar_Syntax_Syntax.n with
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
        let t1 = FStar_Syntax_Util.unmeta t1  in
        let t2 = FStar_Syntax_Util.unmeta t2  in
        match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____2693 = FStar_Syntax_Syntax.fv_eq f g  in
            (match uu____2693 with
             | true  -> FullMatch
             | uu____2694 ->
                 MisMatch
                   ((Some (fv_delta_depth env f)),
                     (Some (fv_delta_depth env g))))
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____2698),FStar_Syntax_Syntax.Tm_uinst (g,uu____2700)) ->
            let _0_337 = head_matches env f g  in
            FStar_All.pipe_right _0_337 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____2715),FStar_Syntax_Syntax.Tm_uvar (uv',uu____2717)) ->
            let uu____2742 = FStar_Unionfind.equivalent uv uv'  in
            (match uu____2742 with
             | true  -> FullMatch
             | uu____2746 -> MisMatch (None, None))
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3284),FStar_Syntax_Syntax.Tm_refine (y,uu____3286)) ->
            let uu____3295 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right _0_338 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____2762),uu____2763) ->
            let _0_339 = head_matches env x.FStar_Syntax_Syntax.sort t2  in
            FStar_All.pipe_right _0_339 head_match
        | (uu____2768,FStar_Syntax_Syntax.Tm_refine (x,uu____2770)) ->
            let _0_340 = head_matches env t1 x.FStar_Syntax_Syntax.sort  in
            FStar_All.pipe_right _0_340 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3317),FStar_Syntax_Syntax.Tm_app (head',uu____3319))
            ->
            let _0_341 = head_matches env head head'  in
            FStar_All.pipe_right _0_341 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____2812),uu____2813) ->
            let _0_342 = head_matches env head t2  in
            FStar_All.pipe_right _0_342 head_match
        | (uu____2828,FStar_Syntax_Syntax.Tm_app (head,uu____2830)) ->
            let _0_343 = head_matches env t1 head  in
            FStar_All.pipe_right _0_343 head_match
        | uu____2845 ->
            MisMatch
              (let _0_345 = delta_depth_of_term env t1  in
               let _0_344 = delta_depth_of_term env t2  in (_0_345, _0_344))
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____2882 = FStar_Syntax_Util.head_and_args t  in
    match uu____2882 with
    | (head,uu____2894) ->
        let uu____2909 =
          (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n  in
        (match uu____2909 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3464 =
               let uu____3465 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right _0_346 FStar_Option.isSome  in
             (match uu____2912 with
              | true  ->
                  let _0_348 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Normalize.Beta;
                      FStar_TypeChecker_Normalize.Eager_unfolding] env t
                     in
                  FStar_All.pipe_right _0_348 (fun _0_347  -> Some _0_347)
              | uu____2924 -> None)
         | uu____2925 -> None)
     in
  let success d r t1 t2 =
    (r,
      (match d > (Prims.parse_int "0") with
       | true  -> Some (t1, t2)
       | uu____2952 -> None))
     in
  let fail r = (r, None)  in
  let rec aux retry n_delta t1 t2 =
    let r = head_matches env t1 t2  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),_)|MisMatch
      (_,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        (match Prims.op_Negation retry with
         | true  -> fail r
         | uu____3004 ->
             let uu____3005 =
               let _0_350 = maybe_inline t1  in
               let _0_349 = maybe_inline t2  in (_0_350, _0_349)  in
             (match uu____3005 with
              | (None ,None ) -> fail r
              | (Some t1,None ) ->
                  aux false (n_delta + (Prims.parse_int "1")) t1 t2
              | (None ,Some t2) ->
                  aux false (n_delta + (Prims.parse_int "1")) t1 t2
              | (Some t1,Some t2) ->
                  aux false (n_delta + (Prims.parse_int "1")) t1 t2))
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3033 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____3033 with
         | None  -> fail r
         | Some d ->
             let t12 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t1
                in
             let t2 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t2
                in
             aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
    | MisMatch (Some d1,Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
        let uu____3048 =
          match d1_greater_than_d2 with
          | true  ->
              let t1' =
                normalize_refinement
                  [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                  FStar_TypeChecker_Normalize.WHNF] env wl t1
                 in
              (t1', t2)
          | uu____3054 ->
              let t2' =
                normalize_refinement
                  [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                  FStar_TypeChecker_Normalize.WHNF] env wl t2
                 in
              let _0_351 =
                normalize_refinement
                  [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                  FStar_TypeChecker_Normalize.WHNF] env wl t2
                 in
              (t1, _0_351)
           in
        (match uu____3048 with
         | (t1,t2) -> aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
    | MisMatch uu____3063 -> fail r
    | uu____3068 -> success n_delta r t1 t2  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3093 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3123 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3138 = FStar_Syntax_Util.type_u ()  in
      match uu____3138 with
      | (t,uu____3142) -> Prims.fst (new_uvar r binders t)
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let _0_352 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right _0_352 Prims.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term) *
        (FStar_Syntax_Syntax.term -> Prims.bool) *
        (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____3188 = head_matches env t t'  in
        match uu____3188 with
        | MisMatch uu____3189 -> false
        | uu____3194 -> true  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3254,imp),T (t,uu____3257)) -> (t, imp)
                     | uu____3274 -> failwith "Bad reconstruction") args
                args'
               in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, args)))
              None t.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3318  ->
                    match uu____3318 with
                    | (t,uu____3326) ->
                        (None, INVARIANT, (T (t, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3359 = failwith "Bad reconstruction"  in
          let uu____3360 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____3360 with
           | (bs,c) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____3981))::tcs2) ->
                       aux
                         (((let uu___135_3435 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___143_4003.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___135_3435.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }), imp) :: out) bs tcs
                   | ([],(C c)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c
                   | uu____3445 -> failwith "Bad reconstruction"  in
                 aux [] bs tcs  in
               let rec decompose out uu___117_3476 =
                 match uu___117_3476 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c)) :: out)
                 | hd::rest ->
                     decompose
                       (((Some hd), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let _0_353 = decompose [] bs  in (rebuild, matches, _0_353))
      | uu____3559 ->
          let rebuild uu___118_3564 =
            match uu___118_3564 with
            | [] -> t
            | uu____3566 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___119_3585  ->
    match uu___119_3585 with
    | T (t,uu____3587) -> t
    | uu____3596 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___120_3599  ->
    match uu___120_3599 with
    | T (t,uu____3601) -> FStar_Syntax_Syntax.as_arg t
    | uu____3610 -> failwith "Impossible"
  
let imitation_sub_probs orig env scope ps qs =
  let r = p_loc orig  in
  let rel = p_rel orig  in
  let sub_prob scope args q =
    match q with
    | (uu____3691,variance,T (ti,mk_kind)) ->
        let k = mk_kind scope r  in
        let uu____3710 = new_uvar r scope k  in
        (match uu____3710 with
         | (gi_xs,gi) ->
             let gi_ps =
               match args with
               | [] -> gi
               | uu____3722 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (gi, args)) None r
                in
             let _0_356 =
               let _0_355 =
                 mk_problem scope orig gi_ps (vary_rel rel variance) ti None
                   "type subterm"
                  in
               FStar_All.pipe_left
                 (fun _0_354  -> FStar_TypeChecker_Common.TProb _0_354)
                 _0_355
                in
             ((T (gi_xs, mk_kind)), _0_356))
    | (uu____3743,uu____3744,C uu____3745) -> failwith "impos"  in
  let rec aux scope args qs =
    match qs with
    | [] -> ([], [], FStar_Syntax_Util.t_true)
    | q::qs ->
        let uu____3832 =
          match q with
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____3843;
               FStar_Syntax_Syntax.pos = uu____3844;
               FStar_Syntax_Syntax.vars = uu____3845;_})
              ->
              let uu____3860 =
                sub_prob scope args (bopt, variance, (T (ti, kind_type)))  in
              (match uu____3860 with
               | (T (gi_xs,uu____3876),prob) ->
                   let _0_359 =
                     let _0_358 = FStar_Syntax_Syntax.mk_Total' gi_xs uopt
                        in
                     FStar_All.pipe_left (fun _0_357  -> C _0_357) _0_358  in
                   (_0_359, [prob])
               | uu____3887 -> failwith "impossible")
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____3897;
               FStar_Syntax_Syntax.pos = uu____3898;
               FStar_Syntax_Syntax.vars = uu____3899;_})
              ->
              let uu____3914 =
                sub_prob scope args (bopt, variance, (T (ti, kind_type)))  in
              (match uu____3914 with
               | (T (gi_xs,uu____3930),prob) ->
                   let _0_362 =
                     let _0_361 = FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                        in
                     FStar_All.pipe_left (fun _0_360  -> C _0_360) _0_361  in
                   (_0_362, [prob])
               | uu____3941 -> failwith "impossible")
          | (uu____3947,uu____3948,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
               FStar_Syntax_Syntax.tk = uu____3950;
               FStar_Syntax_Syntax.pos = uu____3951;
               FStar_Syntax_Syntax.vars = uu____3952;_})
              ->
              let components =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map
                     (fun t  ->
                        (None, INVARIANT, (T ((Prims.fst t), generic_kind)))))
                 in
              let components =
                (None, COVARIANT,
                  (T ((c.FStar_Syntax_Syntax.result_typ), kind_type)))
                :: components  in
              let uu____4026 =
                let _0_363 = FStar_List.map (sub_prob scope args) components
                   in
                FStar_All.pipe_right _0_363 FStar_List.unzip  in
              (match uu____4026 with
               | (tcs,sub_probs) ->
                   let gi_xs =
                     let _0_368 =
                       let _0_367 =
                         let _0_364 = FStar_List.hd tcs  in
                         FStar_All.pipe_right _0_364 un_T  in
                       let _0_366 =
                         let _0_365 = FStar_List.tl tcs  in
                         FStar_All.pipe_right _0_365
                           (FStar_List.map arg_of_tc)
                          in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (c.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           (c.FStar_Syntax_Syntax.effect_name);
                         FStar_Syntax_Syntax.result_typ = _0_367;
                         FStar_Syntax_Syntax.effect_args = _0_366;
                         FStar_Syntax_Syntax.flags =
                           (c.FStar_Syntax_Syntax.flags)
                       }  in
                     FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_368
                      in
                   ((C gi_xs), sub_probs))
          | uu____4059 ->
              let uu____4066 = sub_prob scope args q  in
              (match uu____4066 with | (ktec,prob) -> (ktec, [prob]))
           in
        (match uu____3832 with
         | (tc,probs) ->
             let uu____4084 =
               match q with
               | (Some b,uu____4110,uu____4111) ->
                   let _0_370 =
                     let _0_369 = FStar_Syntax_Util.arg_of_non_null_binder b
                        in
                     _0_369 :: args  in
                   ((Some b), (b :: scope), _0_370)
               | uu____4134 -> (None, scope, args)  in
             (match uu____4084 with
              | (bopt,scope,args) ->
                  let uu____4177 = aux scope args qs  in
                  (match uu____4177 with
                   | (sub_probs,tcs,f) ->
                       let f =
                         match bopt with
                         | None  ->
                             FStar_Syntax_Util.mk_conj_l
                               (let _0_371 =
                                  FStar_All.pipe_right probs
                                    (FStar_List.map
                                       (fun prob  ->
                                          FStar_All.pipe_right (p_guard prob)
                                            Prims.fst))
                                   in
                                f :: _0_371)
                         | Some b ->
                             FStar_Syntax_Util.mk_conj_l
                               (let _0_373 =
                                  FStar_Syntax_Util.mk_forall (Prims.fst b) f
                                   in
                                let _0_372 =
                                  FStar_All.pipe_right probs
                                    (FStar_List.map
                                       (fun prob  ->
                                          FStar_All.pipe_right (p_guard prob)
                                            Prims.fst))
                                   in
                                _0_373 :: _0_372)
                          in
                       ((FStar_List.append probs sub_probs), (tc :: tcs), f))))
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
  let uu___136_4259 = p  in
  let _0_375 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let _0_374 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_4869.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____4872;
    FStar_TypeChecker_Common.relation =
      (uu___144_4869.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____4873;
    FStar_TypeChecker_Common.element =
      (uu___144_4869.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_4869.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_4869.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_4869.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_4869.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___136_4259.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_377 = compress_tprob wl p  in
          FStar_All.pipe_right _0_377
            (fun _0_376  -> FStar_TypeChecker_Common.TProb _0_376)
      | FStar_TypeChecker_Common.CProb uu____4273 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let _0_378 = compress_prob wl pr  in
        FStar_All.pipe_right _0_378 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4292 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____4292 with
           | (lh,uu____4305) ->
               let uu____4320 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____4320 with
                | (rh,uu____4333) ->
                    let uu____4348 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4973,FStar_Syntax_Syntax.Tm_uvar uu____4974)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4999,uu____5000)
                          ->
                          let uu____5009 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____4393 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5049 ->
                                    let rank =
                                      let uu____4440 = is_top_level_prob prob
                                         in
                                      match uu____4440 with
                                      | true  -> flex_refine
                                      | uu____4441 -> flex_refine_inner  in
                                    let _0_380 =
                                      let uu___137_4444 = tp  in
                                      let _0_379 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___145_5061.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___145_5061.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___145_5061.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5064;
                                        FStar_TypeChecker_Common.element =
                                          (uu___145_5061.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___145_5061.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___145_5061.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___145_5061.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___145_5061.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___137_4444.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, _0_380)))
                      | (uu____4454,FStar_Syntax_Syntax.Tm_uvar uu____4455)
                          ->
                          let uu____5084 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____4464 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____4504 ->
                                    let _0_382 =
                                      let uu___138_4514 = tp  in
                                      let _0_381 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___146_5135.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5138;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___146_5135.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___146_5135.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___146_5135.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___146_5135.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___146_5135.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___146_5135.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___146_5135.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___138_4514.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, _0_382)))
                      | (uu____4526,uu____4527) -> (rigid_rigid, tp)  in
                    (match uu____4348 with
                     | (rank,tp) ->
                         let _0_384 =
                           FStar_All.pipe_right
                             (let uu___139_4540 = tp  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___147_5169.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___147_5169.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___147_5169.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___147_5169.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___147_5169.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___147_5169.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___147_5169.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___147_5169.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___147_5169.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_383  ->
                                FStar_TypeChecker_Common.TProb _0_383)
                            in
                         (rank, _0_384))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5175 =
            FStar_All.pipe_right
              (let uu___140_4548 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___148_5178.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___148_5178.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___148_5178.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___148_5178.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___148_5178.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___148_5178.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___148_5178.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___148_5178.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___148_5178.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_385  -> FStar_TypeChecker_Common.CProb _0_385)
             in
          (rigid_rigid, _0_386)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option *
      FStar_TypeChecker_Common.prob Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____5210 probs =
      match uu____5210 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min, out, min_rank)
           | hd::tl ->
               let uu____4610 = rank wl hd  in
               (match uu____4610 with
                | (rank,hd) ->
                    (match rank <= flex_rigid_eq with
                     | true  ->
                         (match min with
                          | None  ->
                              ((Some hd), (FStar_List.append out tl), rank)
                          | Some m ->
                              ((Some hd), (FStar_List.append out (m :: tl)),
                                rank))
                     | uu____4635 ->
                         (match rank < min_rank with
                          | true  ->
                              (match min with
                               | None  -> aux (rank, (Some hd), out) tl
                               | Some m ->
                                   aux (rank, (Some hd), (m :: out)) tl)
                          | uu____4651 -> aux (min_rank, min, (hd :: out)) tl))))
       in
    aux ((flex_flex + (Prims.parse_int "1")), None, []) wl.attempting
  
let is_flex_rigid : Prims.int -> Prims.bool =
  fun rank  -> (flex_refine_inner <= rank) && (rank <= flex_rigid) 
let is_rigid_flex : Prims.int -> Prims.bool =
  fun rank  -> (rigid_flex <= rank) && (rank <= refine_flex) 
type univ_eq_sol =
  | UDeferred of worklist 
  | USolved of worklist 
  | UFailed of Prims.string 
let uu___is_UDeferred : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____4675 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____4687 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____4699 -> false
  
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
          let u1 = FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1
             in
          let u2 = FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2
             in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u  ->
                        let uu____4736 = FStar_Syntax_Util.univ_kernel u  in
                        match uu____4736 with
                        | (k,uu____4740) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____4745 -> false)))
            | uu____4746 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let try_umax_components u1 u2 msg =
            match (u1, u2) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                (match (FStar_List.length us1) = (FStar_List.length us2) with
                 | true  ->
                     let rec aux wl us1 us2 =
                       match (us1, us2) with
                       | (u1::us1,u2::us2) ->
                           let uu____4789 =
                             really_solve_universe_eq pid_orig wl u1 u2  in
                           (match uu____4789 with
                            | USolved wl -> aux wl us1 us2
                            | failed -> failed)
                       | uu____4792 -> USolved wl  in
                     aux wl us1 us2
                 | uu____4797 ->
                     UFailed
                       (let _0_388 = FStar_Syntax_Print.univ_to_string u1  in
                        let _0_387 = FStar_Syntax_Print.univ_to_string u2  in
                        FStar_Util.format2
                          "Unable to unify universes: %s and %s" _0_388
                          _0_387))
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl us =
                  match us with
                  | [] -> USolved wl
                  | u::us ->
                      let uu____4814 =
                        really_solve_universe_eq pid_orig wl u u'  in
                      (match uu____4814 with
                       | USolved wl -> aux wl us
                       | failed -> failed)
                   in
                aux wl us
            | uu____4817 ->
                UFailed
                  (let _0_390 = FStar_Syntax_Print.univ_to_string u1  in
                   let _0_389 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format3
                     "Unable to unify universes: %s and %s (%s)" _0_390
                     _0_389 msg)
             in
          match (u1, u2) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              failwith
                (let _0_392 = FStar_Syntax_Print.univ_to_string u1  in
                 let _0_391 = FStar_Syntax_Print.univ_to_string u2  in
                 FStar_Util.format2
                   "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                   _0_392 _0_391)
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____4837 = FStar_Unionfind.equivalent v1 v2  in
              (match uu____4837 with
               | true  -> USolved wl
               | uu____4839 ->
                   let wl = extend_solution pid_orig [UNIV (v1, u2)] wl  in
                   USolved wl)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u = norm_univ wl u  in
              let uu____4850 = occurs_univ v1 u  in
              (match uu____4850 with
               | true  ->
                   let _0_395 =
                     let _0_394 =
                       FStar_Syntax_Print.univ_to_string
                         (FStar_Syntax_Syntax.U_unif v1)
                        in
                     let _0_393 = FStar_Syntax_Print.univ_to_string u  in
                     FStar_Util.format2
                       "Failed occurs check: %s occurs in %s" _0_394 _0_393
                      in
                   try_umax_components u1 u2 _0_395
               | uu____4851 ->
                   USolved (extend_solution pid_orig [UNIV (v1, u)] wl))
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              (match wl.defer_ok with
               | true  -> UDeferred wl
               | uu____4858 ->
                   let u1 = norm_univ wl u1  in
                   let u2 = norm_univ wl u2  in
                   let uu____4861 = FStar_Syntax_Util.eq_univs u1 u2  in
                   (match uu____4861 with
                    | true  -> USolved wl
                    | uu____4862 -> try_umax_components u1 u2 ""))
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
          match (wl.tcenv).FStar_TypeChecker_Env.lax_universes with
          | true  -> USolved wl
          | uu____4883 -> really_solve_universe_eq orig wl u1 u2
  
let match_num_binders bc1 bc2 =
  let uu____4932 = bc1  in
  match uu____4932 with
  | (bs1,mk_cod1) ->
      let uu____4957 = bc2  in
      (match uu____4957 with
       | (bs2,mk_cod2) ->
           let curry n bs mk_cod =
             let uu____5004 = FStar_Util.first_N n bs  in
             match uu____5004 with
             | (bs,rest) -> let _0_396 = mk_cod rest  in (bs, _0_396)  in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           (match l1 = l2 with
            | true  ->
                let _0_400 = let _0_397 = mk_cod1 []  in (bs1, _0_397)  in
                let _0_399 = let _0_398 = mk_cod2 []  in (bs2, _0_398)  in
                (_0_400, _0_399)
            | uu____5043 ->
                (match l1 > l2 with
                 | true  ->
                     let _0_403 = curry l2 bs1 mk_cod1  in
                     let _0_402 = let _0_401 = mk_cod2 []  in (bs2, _0_401)
                        in
                     (_0_403, _0_402)
                 | uu____5067 ->
                     let _0_406 = let _0_404 = mk_cod1 []  in (bs1, _0_404)
                        in
                     let _0_405 = curry l1 bs2 mk_cod2  in (_0_406, _0_405))))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5841 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       match uu____5169 with
       | true  ->
           let _0_407 = wl_to_string probs  in
           FStar_Util.print1 "solve:\n\t%s\n" _0_407
       | uu____5170 -> ());
      (let uu____5171 = next_prob probs  in
       match uu____5171 with
       | (Some hd,tl,rank) ->
           let probs =
             let uu___141_5184 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___141_5184.wl_deferred);
               ctr = (uu___141_5184.ctr);
               defer_ok = (uu___141_5184.defer_ok);
               smt_ok = (uu___141_5184.smt_ok);
               tcenv = (uu___141_5184.tcenv)
             }  in
           (match hd with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs1
            | FStar_TypeChecker_Common.TProb tp ->
                (match ((Prims.op_Negation probs.defer_ok) &&
                          (flex_refine_inner <= rank))
                         && (rank <= flex_rigid)
                 with
                 | true  ->
                     let uu____5191 = solve_flex_rigid_join env tp probs  in
                     (match uu____5191 with
                      | None  -> solve_t' env (maybe_invert tp) probs
                      | Some wl -> solve env wl)
                 | uu____5194 ->
                     (match ((Prims.op_Negation probs.defer_ok) &&
                               (rigid_flex <= rank))
                              && (rank <= refine_flex)
                      with
                      | true  ->
                          let uu____5195 = solve_rigid_flex_meet env tp probs
                             in
                          (match uu____5195 with
                           | None  -> solve_t' env (maybe_invert tp) probs
                           | Some wl -> solve env wl)
                      | uu____5198 -> solve_t' env (maybe_invert tp) probs)))
       | (None ,uu____5199,uu____5200) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5882 ->
                let uu____5887 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5242  ->
                          match uu____5242 with
                          | (c,uu____5247,uu____5248) -> c < probs.ctr))
                   in
                (match uu____5214 with
                 | (attempt,rest) ->
                     (match attempt with
                      | [] ->
                          Success
                            (FStar_List.map
                               (fun uu____5275  ->
                                  match uu____5275 with
                                  | (uu____5281,x,y) -> (x, y))
                               probs.wl_deferred)
                      | uu____5284 ->
                          let _0_409 =
                            let uu___142_5289 = probs  in
                            let _0_408 =
                              FStar_All.pipe_right attempt
                                (FStar_List.map
                                   (fun uu____5298  ->
                                      match uu____5298 with
                                      | (uu____5302,uu____5303,y) -> y))
                               in
                            {
                              attempting = uu____5965;
                              wl_deferred = rest;
                              ctr = (uu___142_5289.ctr);
                              defer_ok = (uu___142_5289.defer_ok);
                              smt_ok = (uu___142_5289.smt_ok);
                              tcenv = (uu___142_5289.tcenv)
                            }  in
                          solve env _0_409))))

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
            let uu____5310 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____5310 with
            | USolved wl ->
                let _0_410 = solve_prob orig None [] wl  in solve env _0_410
            | UFailed msg -> giveup env msg orig
            | UDeferred wl -> solve env (defer "" orig wl)

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
              | ([],[]) -> USolved wl
              | (u1::us1,u2::us2) ->
                  let uu____5345 = solve_universe_eq (p_pid orig) wl u1 u2
                     in
                  (match uu____5345 with
                   | USolved wl -> aux wl us1 us2
                   | failed_or_deferred -> failed_or_deferred)
              | uu____5348 -> UFailed "Unequal number of universes"  in
            let t1 = whnf env t1  in
            let t2 = whnf env t2  in
            match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6033;
                  FStar_Syntax_Syntax.pos = uu____6034;
                  FStar_Syntax_Syntax.vars = uu____6035;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____5361;
                  FStar_Syntax_Syntax.pos = uu____5362;
                  FStar_Syntax_Syntax.vars = uu____5363;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____5379 -> USolved wl

and giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          match wl.defer_ok with
          | true  ->
              ((let uu____5387 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel")
                   in
                match uu____5387 with
                | true  ->
                    let _0_411 = prob_to_string env orig  in
                    FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                      _0_411 msg
                | uu____5388 -> ());
               solve env (defer msg orig wl))
          | uu____5389 -> giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6073 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         match uu____5395 with
         | true  ->
             let _0_412 =
               FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
             FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
               _0_412
         | uu____5396 -> ());
        (let uu____5397 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____5397 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____5439 = head_matches_delta env () t1 t2  in
               match uu____5439 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6140 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6166 =
                          match ts with
                          | Some (t1,t2) ->
                              let _0_414 = FStar_Syntax_Subst.compress t1  in
                              let _0_413 = FStar_Syntax_Subst.compress t2  in
                              (_0_414, _0_413)
                          | None  ->
                              let _0_416 = FStar_Syntax_Subst.compress t1  in
                              let _0_415 = FStar_Syntax_Subst.compress t2  in
                              (_0_416, _0_415)
                           in
                        (match uu____5487 with
                         | (t1,t2) ->
                             let eq_prob t1 t2 =
                               let _0_418 =
                                 new_problem env t1
                                   FStar_TypeChecker_Common.EQ t2 None
                                   t1.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_417  ->
                                    FStar_TypeChecker_Common.TProb _0_417)
                                 _0_418
                                in
                             (match ((t1.FStar_Syntax_Syntax.n),
                                      (t2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  Some
                                    (let _0_422 =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_refine
                                             (let _0_419 =
                                                FStar_Syntax_Util.mk_disj
                                                  phi1 phi2
                                                 in
                                              (x, _0_419)))) None
                                         t1.FStar_Syntax_Syntax.pos
                                        in
                                     let _0_421 =
                                       let _0_420 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           y.FStar_Syntax_Syntax.sort
                                          in
                                       [_0_420]  in
                                     (_0_422, _0_421))
                              | (uu____5561,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5563)) ->
                                  Some
                                    (let _0_424 =
                                       let _0_423 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           t1
                                          in
                                       [_0_423]  in
                                     (t1, _0_424))
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5573),uu____5574) ->
                                  Some
                                    (let _0_426 =
                                       let _0_425 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           t2
                                          in
                                       [_0_425]  in
                                     (t2, _0_426))
                              | uu____5583 ->
                                  let uu____5586 =
                                    FStar_Syntax_Util.head_and_args t1  in
                                  (match uu____5586 with
                                   | (head1,uu____5601) ->
                                       let uu____5616 =
                                         (FStar_Syntax_Util.un_uinst head1).FStar_Syntax_Syntax.n
                                          in
                                       (match uu____5616 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6344;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6346;_}
                                            ->
                                            let prev =
                                              match i > (Prims.parse_int "1")
                                              with
                                              | true  ->
                                                  FStar_Syntax_Syntax.Delta_defined_at_level
                                                    (i -
                                                       (Prims.parse_int "1"))
                                              | uu____5629 ->
                                                  FStar_Syntax_Syntax.Delta_constant
                                               in
                                            let t1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t1
                                               in
                                            let t2 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t2
                                               in
                                            disjoin t1 t2
                                        | uu____5632 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6364) ->
                  let uu____6377 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___124_6386  ->
                            match uu___124_6386 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6391 =
                                       FStar_Syntax_Util.head_and_args
                                         tp.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____5668 with
                                      | (u',uu____5679) ->
                                          let uu____5694 =
                                            (whnf env u').FStar_Syntax_Syntax.n
                                             in
                                          (match uu____5694 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6422) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____5712 -> false))
                                 | uu____5713 -> false)
                            | uu____5715 -> false))
                     in
                  (match uu____5654 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6462 tps =
                         match uu____6462 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6489 =
                                    let uu____6494 =
                                      whnf env
                                        hd.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound _0_427  in
                                  (match uu____5763 with
                                   | Some (bound,sub) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____5786 -> None)
                          in
                       let uu____5791 =
                         let _0_429 =
                           let _0_428 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (_0_428, [])  in
                         make_lower_bound _0_429 lower_bounds  in
                       (match uu____5791 with
                        | None  ->
                            ((let uu____6534 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              match uu____5802 with
                              | true  ->
                                  FStar_Util.print_string "No lower bounds\n"
                              | uu____5803 -> ());
                             None)
                        | Some (lhs_bound,sub_probs) ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____5815 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              match uu____5815 with
                              | true  ->
                                  let wl' =
                                    let uu___143_5817 = wl  in
                                    {
                                      attempting =
                                        ((FStar_TypeChecker_Common.TProb
                                            eq_prob) :: sub_probs);
                                      wl_deferred =
                                        (uu___143_5817.wl_deferred);
                                      ctr = (uu___143_5817.ctr);
                                      defer_ok = (uu___143_5817.defer_ok);
                                      smt_ok = (uu___143_5817.smt_ok);
                                      tcenv = (uu___143_5817.tcenv)
                                    }  in
                                  let _0_430 = wl_to_string wl'  in
                                  FStar_Util.print1
                                    "After meeting refinements: %s\n" _0_430
                              | uu____5818 -> ());
                             (let uu____5819 =
                                solve_t env eq_prob
                                  (let uu___144_5820 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___144_5820.wl_deferred);
                                     ctr = (uu___144_5820.ctr);
                                     defer_ok = (uu___144_5820.defer_ok);
                                     smt_ok = (uu___144_5820.smt_ok);
                                     tcenv = (uu___144_5820.tcenv)
                                   })
                                 in
                              match uu____5819 with
                              | Success uu____5822 ->
                                  let wl =
                                    let uu___145_5824 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___145_5824.wl_deferred);
                                      ctr = (uu___145_5824.ctr);
                                      defer_ok = (uu___145_5824.defer_ok);
                                      smt_ok = (uu___145_5824.smt_ok);
                                      tcenv = (uu___145_5824.tcenv)
                                    }  in
                                  let wl =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl
                                     in
                                  let uu____5826 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl) wl
                                      lower_bounds
                                     in
                                  Some wl
                              | uu____5829 -> None))))
              | uu____5830 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6570 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         match uu____5837 with
         | true  ->
             let _0_431 =
               FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
             FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
               _0_431
         | uu____5838 -> ());
        (let uu____5839 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____5839 with
         | (u,args) ->
             let uu____6600 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____5866 with
              | (ok,head_match,partial_match,fallback,failed_match) ->
                  let max i j =
                    match i < j with | true  -> j | uu____5885 -> i  in
                  let base_types_match t1 t2 =
                    let uu____5897 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____5897 with
                    | (h1,args1) ->
                        let uu____5925 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____5925 with
                         | (h2,uu____5938) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____5957 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  (match uu____5957 with
                                   | true  ->
                                       (match (FStar_List.length args1) =
                                                (Prims.parse_int "0")
                                        with
                                        | true  -> Some []
                                        | uu____5969 ->
                                            Some
                                              (let _0_434 =
                                                 let _0_433 =
                                                   new_problem env t1
                                                     FStar_TypeChecker_Common.EQ
                                                     t2 None
                                                     t1.FStar_Syntax_Syntax.pos
                                                     "joining refinements"
                                                    in
                                                 FStar_All.pipe_left
                                                   (fun _0_432  ->
                                                      FStar_TypeChecker_Common.TProb
                                                        _0_432) _0_433
                                                  in
                                               [_0_434]))
                                   | uu____5973 -> None)
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  (match FStar_Syntax_Syntax.bv_eq a b with
                                   | true  ->
                                       (match (FStar_List.length args1) =
                                                (Prims.parse_int "0")
                                        with
                                        | true  -> Some []
                                        | uu____5988 ->
                                            Some
                                              (let _0_437 =
                                                 let _0_436 =
                                                   new_problem env t1
                                                     FStar_TypeChecker_Common.EQ
                                                     t2 None
                                                     t1.FStar_Syntax_Syntax.pos
                                                     "joining refinements"
                                                    in
                                                 FStar_All.pipe_left
                                                   (fun _0_435  ->
                                                      FStar_TypeChecker_Common.TProb
                                                        _0_435) _0_436
                                                  in
                                               [_0_437]))
                                   | uu____5992 -> None)
                              | uu____5994 -> None))
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
                         | Some m ->
                             let x = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x)]
                                in
                             let phi1 = FStar_Syntax_Subst.subst subst phi1
                                in
                             let phi2 = FStar_Syntax_Subst.subst subst phi2
                                in
                             Some
                               (let _0_439 =
                                  let _0_438 =
                                    FStar_Syntax_Util.mk_conj phi1 phi2  in
                                  FStar_Syntax_Util.refine x _0_438  in
                                (_0_439, m)))
                    | (uu____6068,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6070)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6858),uu____6859) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m -> Some (t1, m))
                    | uu____6134 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m -> Some (t1, m))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6924) ->
                       let uu____6937 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___125_6946  ->
                                 match uu___125_6946 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____6951 =
                                            FStar_Syntax_Util.head_and_args
                                              tp.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____6195 with
                                           | (u',uu____6206) ->
                                               let uu____6221 =
                                                 (whnf env u').FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____6221 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6982) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6239 -> false))
                                      | uu____6240 -> false)
                                 | uu____6242 -> false))
                          in
                       (match uu____6181 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7026 tps =
                              match uu____7026 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7067 =
                                         let uu____7074 =
                                           whnf env
                                             hd.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound _0_440  in
                                       (match uu____6308 with
                                        | Some (bound,sub) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____6347 -> None)
                               in
                            let uu____6354 =
                              let _0_442 =
                                let _0_441 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (_0_441, [])  in
                              make_upper_bound _0_442 upper_bounds  in
                            (match uu____6354 with
                             | None  ->
                                 ((let uu____7138 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   match uu____6369 with
                                   | true  ->
                                       FStar_Util.print_string
                                         "No upper bounds\n"
                                   | uu____6370 -> ());
                                  None)
                             | Some (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     None tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____6388 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   match uu____6388 with
                                   | true  ->
                                       let wl' =
                                         let uu___146_6390 = wl  in
                                         {
                                           attempting =
                                             ((FStar_TypeChecker_Common.TProb
                                                 eq_prob) :: sub_probs);
                                           wl_deferred =
                                             (uu___146_6390.wl_deferred);
                                           ctr = (uu___146_6390.ctr);
                                           defer_ok =
                                             (uu___146_6390.defer_ok);
                                           smt_ok = (uu___146_6390.smt_ok);
                                           tcenv = (uu___146_6390.tcenv)
                                         }  in
                                       let _0_443 = wl_to_string wl'  in
                                       FStar_Util.print1
                                         "After joining refinements: %s\n"
                                         _0_443
                                   | uu____6391 -> ());
                                  (let uu____6392 =
                                     solve_t env eq_prob
                                       (let uu___147_6393 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___147_6393.wl_deferred);
                                          ctr = (uu___147_6393.ctr);
                                          defer_ok = (uu___147_6393.defer_ok);
                                          smt_ok = (uu___147_6393.smt_ok);
                                          tcenv = (uu___147_6393.tcenv)
                                        })
                                      in
                                   match uu____6392 with
                                   | Success uu____6395 ->
                                       let wl =
                                         let uu___148_6397 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___156_7167.wl_deferred);
                                           ctr = (uu___156_7167.ctr);
                                           defer_ok =
                                             (uu___148_6397.defer_ok);
                                           smt_ok = (uu___148_6397.smt_ok);
                                           tcenv = (uu___148_6397.tcenv)
                                         }  in
                                       let wl =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl
                                          in
                                       let uu____6399 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None [] wl)
                                           wl upper_bounds
                                          in
                                       Some wl
                                   | uu____6402 -> None))))
                   | uu____6403 -> failwith "Impossible: Not a flex-rigid")))

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
                    let rhs_prob = rhs (FStar_List.rev scope) env subst  in
                    ((let uu____6468 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      match uu____6468 with
                      | true  ->
                          let _0_444 = prob_to_string env rhs_prob  in
                          FStar_Util.print1 "rhs_prob = %s\n" _0_444
                      | uu____6469 -> ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst  in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs,(hd2,imp')::ys) when imp = imp' ->
                    let hd1 =
                      let uu___149_6500 = hd1  in
                      let _0_445 =
                        FStar_Syntax_Subst.subst subst
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___157_7271.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___149_6500.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = _0_445
                      }  in
                    let hd2 =
                      let uu___150_6502 = hd2  in
                      let _0_446 =
                        FStar_Syntax_Subst.subst subst
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___158_7276.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___150_6502.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = _0_446
                      }  in
                    let prob =
                      let _0_449 =
                        let _0_448 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd1.FStar_Syntax_Syntax.sort
                          _0_448 hd2.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_447  -> FStar_TypeChecker_Common.TProb _0_447)
                        _0_449
                       in
                    let hd1 = FStar_Syntax_Syntax.freshen_bv hd1  in
                    let subst =
                      let _0_450 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd1))
                        :: _0_450
                       in
                    let env = FStar_TypeChecker_Env.push_bv env hd1  in
                    let uu____6512 =
                      aux ((hd1, imp) :: scope) env subst xs ys  in
                    (match uu____6512 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi =
                           let _0_452 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst
                              in
                           let _0_451 =
                             FStar_Syntax_Util.close_forall [(hd1, imp)] phi
                              in
                           FStar_Syntax_Util.mk_conj _0_452 _0_451  in
                         ((let uu____6537 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           match uu____6537 with
                           | true  ->
                               let _0_454 =
                                 FStar_Syntax_Print.term_to_string phi  in
                               let _0_453 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                                 _0_454 _0_453
                           | uu____6538 -> ());
                          FStar_Util.Inl ((prob :: sub_probs), phi))
                     | fail -> fail)
                | uu____6552 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____6558 = aux scope env [] bs1 bs2  in
              match uu____6558 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let _0_455 = compress_tprob wl problem  in solve_t' env _0_455 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env orig wl head1 head2 t1 t2 =
          let uu____6606 = head_matches_delta env wl t1 t2  in
          match uu____6606 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7411,uu____7412) ->
                   let may_relate head3 =
                     let uu____7427 =
                       let uu____7428 = FStar_Syntax_Util.un_uinst head3 in
                       uu____7428.FStar_Syntax_Syntax.n in
                     match uu____7427 with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____6646 -> false  in
                   (match ((may_relate head1) || (may_relate head2)) &&
                            wl.smt_ok
                    with
                    | true  ->
                        let guard =
                          match problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                          with
                          | true  ->
                              FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun
                                FStar_Syntax_Syntax.tun t1 t2
                          | uu____6652 ->
                              let has_type_guard t1 t2 =
                                match problem.FStar_TypeChecker_Common.element
                                with
                                | Some t ->
                                    FStar_Syntax_Util.mk_has_type t1 t t2
                                | None  ->
                                    let x =
                                      FStar_Syntax_Syntax.new_bv None t1  in
                                    let _0_457 =
                                      let _0_456 =
                                        FStar_Syntax_Syntax.bv_to_name x  in
                                      FStar_Syntax_Util.mk_has_type t1 _0_456
                                        t2
                                       in
                                    FStar_Syntax_Util.mk_forall x _0_457
                                 in
                              (match problem.FStar_TypeChecker_Common.relation
                                       = FStar_TypeChecker_Common.SUB
                               with
                               | true  -> has_type_guard t1 t2
                               | uu____6668 -> has_type_guard t2 t1)
                           in
                        let _0_458 = solve_prob orig (Some guard) [] wl  in
                        solve env _0_458
                    | uu____6671 -> giveup env "head mismatch" orig)
               | (uu____6672,Some (t1,t2)) ->
                   solve_t env
                     (let uu___151_6680 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___159_7465.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___159_7465.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___159_7465.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___159_7465.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___159_7465.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___159_7465.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___159_7465.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_6680.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____6681,None ) ->
                   ((let uu____6688 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     match uu____6688 with
                     | true  ->
                         let _0_462 = FStar_Syntax_Print.term_to_string t1
                            in
                         let _0_461 = FStar_Syntax_Print.tag_of_term t1  in
                         let _0_460 = FStar_Syntax_Print.term_to_string t2
                            in
                         let _0_459 = FStar_Syntax_Print.tag_of_term t2  in
                         FStar_Util.print4
                           "Head matches: %s (%s) and %s (%s)\n" _0_462
                           _0_461 _0_460 _0_459
                     | uu____6689 -> ());
                    (let uu____6690 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____6690 with
                     | (head1,args1) ->
                         let uu____6716 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____6716 with
                          | (head2,args2) ->
                              let nargs = FStar_List.length args1  in
                              (match nargs <> (FStar_List.length args2) with
                               | true  ->
                                   let _0_467 =
                                     let _0_466 =
                                       FStar_Syntax_Print.term_to_string
                                         head1
                                        in
                                     let _0_465 = args_to_string args1  in
                                     let _0_464 =
                                       FStar_Syntax_Print.term_to_string
                                         head2
                                        in
                                     let _0_463 = args_to_string args2  in
                                     FStar_Util.format4
                                       "unequal number of arguments: %s[%s] and %s[%s]"
                                       _0_466 _0_465 _0_464 _0_463
                                      in
                                   giveup env _0_467 orig
                               | uu____6756 ->
                                   let uu____6757 =
                                     (nargs = (Prims.parse_int "0")) ||
                                       (let _0_468 =
                                          FStar_Syntax_Util.eq_args args1
                                            args2
                                           in
                                        _0_468 = FStar_Syntax_Util.Equal)
                                      in
                                   (match uu____6757 with
                                    | true  ->
                                        let uu____6760 =
                                          solve_maybe_uinsts env orig head1
                                            head2 wl
                                           in
                                        (match uu____6760 with
                                         | USolved wl ->
                                             let _0_469 =
                                               solve_prob orig None [] wl  in
                                             solve env _0_469
                                         | UFailed msg -> giveup env msg orig
                                         | UDeferred wl ->
                                             solve env
                                               (defer "universe constraints"
                                                  orig wl))
                                    | uu____6764 ->
                                        let uu____6765 =
                                          base_and_refinement env wl t1  in
                                        (match uu____6765 with
                                         | (base1,refinement1) ->
                                             let uu____6791 =
                                               base_and_refinement env wl t2
                                                in
                                             (match uu____6791 with
                                              | (base2,refinement2) ->
                                                  (match (refinement1,
                                                           refinement2)
                                                   with
                                                   | (None ,None ) ->
                                                       let uu____6845 =
                                                         solve_maybe_uinsts
                                                           env orig head1
                                                           head2 wl
                                                          in
                                                       (match uu____6845 with
                                                        | UFailed msg ->
                                                            giveup env msg
                                                              orig
                                                        | UDeferred wl ->
                                                            solve env
                                                              (defer
                                                                 "universe constraints"
                                                                 orig wl)
                                                        | USolved wl ->
                                                            let subprobs =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____6855
                                                                    ->
                                                                   fun
                                                                    uu____6856
                                                                     ->
                                                                    match 
                                                                    (uu____6855,
                                                                    uu____6856)
                                                                    with
                                                                    | 
                                                                    ((a,uu____6866),
                                                                    (a',uu____6868))
                                                                    ->
                                                                    let uu____7669
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
                                                                    _0_48  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_470)
                                                                    _0_471)
                                                                args1 args2
                                                               in
                                                            let formula =
                                                              FStar_Syntax_Util.mk_conj_l
                                                                (FStar_List.map
                                                                   (fun p  ->
                                                                    Prims.fst
                                                                    (p_guard
                                                                    p))
                                                                   subprobs)
                                                               in
                                                            let wl =
                                                              solve_prob orig
                                                                (Some formula)
                                                                [] wl
                                                               in
                                                            solve env
                                                              (attempt
                                                                 subprobs wl))
                                                   | uu____6878 ->
                                                       let lhs =
                                                         force_refinement
                                                           (base1,
                                                             refinement1)
                                                          in
                                                       let rhs =
                                                         force_refinement
                                                           (base2,
                                                             refinement2)
                                                          in
                                                       solve_t env
                                                         (let uu___152_6911 =
                                                            problem  in
                                                          {
                                                            FStar_TypeChecker_Common.pid
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.pid);
                                                            FStar_TypeChecker_Common.lhs
                                                              = lhs;
                                                            FStar_TypeChecker_Common.relation
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.relation);
                                                            FStar_TypeChecker_Common.rhs
                                                              = rhs;
                                                            FStar_TypeChecker_Common.element
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.element);
                                                            FStar_TypeChecker_Common.logical_guard
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.logical_guard);
                                                            FStar_TypeChecker_Common.scope
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.scope);
                                                            FStar_TypeChecker_Common.reason
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.reason);
                                                            FStar_TypeChecker_Common.loc
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.loc);
                                                            FStar_TypeChecker_Common.rank
                                                              =
                                                              (uu___152_6911.FStar_TypeChecker_Common.rank)
                                                          }) wl)))))))))
           in
        let imitate orig env wl p =
          let uu____6931 = p  in
          match uu____6931 with
          | (((u,k),xs,c),ps,(h,uu____6942,qs)) ->
              let xs = sn_binders env xs  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let uu____6991 = imitation_sub_probs orig env xs ps qs  in
              (match uu____6991 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let _0_476 = h gs_xs  in
                     let _0_475 =
                       let _0_474 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_472  -> FStar_Util.Inl _0_472)
                          in
                       FStar_All.pipe_right _0_474
                         (fun _0_473  -> Some _0_473)
                        in
                     FStar_Syntax_Util.abs xs _0_476 _0_475  in
                   ((let uu____7030 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     match uu____7030 with
                     | true  ->
                         let _0_483 =
                           FStar_Syntax_Print.binders_to_string ", " xs  in
                         let _0_482 = FStar_Syntax_Print.comp_to_string c  in
                         let _0_481 = FStar_Syntax_Print.term_to_string im
                            in
                         let _0_480 = FStar_Syntax_Print.tag_of_term im  in
                         let _0_479 =
                           let _0_477 =
                             FStar_List.map (prob_to_string env) sub_probs
                              in
                           FStar_All.pipe_right _0_477
                             (FStar_String.concat ", ")
                            in
                         let _0_478 =
                           FStar_TypeChecker_Normalize.term_to_string env
                             formula
                            in
                         FStar_Util.print6
                           "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                           _0_483 _0_482 _0_481 _0_480 _0_479 _0_478
                     | uu____7032 -> ());
                    (let wl =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl
                        in
                     solve env (attempt sub_probs wl))))
           in
        let imitate' orig env wl uu___123_7049 =
          match uu___123_7049 with
          | None  -> giveup env "unable to compute subterms" orig
          | Some p -> imitate orig env wl p  in
        let project orig env wl i p =
          let uu____7078 = p  in
          match uu____7078 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let uu____7136 = FStar_List.nth ps i  in
              (match uu____7136 with
               | (pi,uu____7139) ->
                   let uu____7144 = FStar_List.nth xs i  in
                   (match uu____7144 with
                    | (xi,uu____7151) ->
                        let rec gs k =
                          let uu____7160 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____7160 with
                          | (bs,k) ->
                              let rec aux subst bs =
                                match bs with
                                | [] -> ([], [])
                                | (a,uu____8035)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____7220 = new_uvar r xs k_a  in
                                    (match uu____7220 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env gi_xs
                                            in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r
                                            in
                                         let subst =
                                           (FStar_Syntax_Syntax.NT (a, gi_xs))
                                           :: subst  in
                                         let uu____7239 = aux subst tl  in
                                         (match uu____7239 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8077 =
                                                let uu____8079 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs
                                                   in
                                                _0_484 :: gi_xs'  in
                                              let _0_486 =
                                                let _0_485 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                _0_485 :: gi_ps'  in
                                              (_0_487, _0_486)))
                                 in
                              aux [] bs
                           in
                        let uu____7256 =
                          let _0_488 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation _0_488  in
                        (match uu____7256 with
                         | true  -> None
                         | uu____7258 ->
                             let uu____7259 = gs xi.FStar_Syntax_Syntax.sort
                                in
                             (match uu____7259 with
                              | (g_xs,uu____7266) ->
                                  let xi = FStar_Syntax_Syntax.bv_to_name xi
                                     in
                                  let proj =
                                    let _0_493 =
                                      (FStar_Syntax_Syntax.mk_Tm_app xi g_xs)
                                        None r
                                       in
                                    let _0_492 =
                                      let _0_491 =
                                        FStar_All.pipe_right
                                          (FStar_Syntax_Util.lcomp_of_comp c)
                                          (fun _0_489  ->
                                             FStar_Util.Inl _0_489)
                                         in
                                      FStar_All.pipe_right _0_491
                                        (fun _0_490  -> Some _0_490)
                                       in
                                    FStar_Syntax_Util.abs xs _0_493 _0_492
                                     in
                                  let sub =
                                    let _0_498 =
                                      let _0_497 =
                                        (FStar_Syntax_Syntax.mk_Tm_app proj
                                           ps) None r
                                         in
                                      let _0_496 =
                                        let _0_495 =
                                          FStar_List.map
                                            (fun uu____7319  ->
                                               match uu____7319 with
                                               | (uu____7324,uu____7325,y) ->
                                                   y) qs
                                           in
                                        FStar_All.pipe_left h _0_495  in
                                      mk_problem (p_scope orig) orig _0_497
                                        (p_rel orig) _0_496 None "projection"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_494  ->
                                         FStar_TypeChecker_Common.TProb
                                           _0_494) _0_498
                                     in
                                  ((let uu____7330 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    match uu____7330 with
                                    | true  ->
                                        let _0_500 =
                                          FStar_Syntax_Print.term_to_string
                                            proj
                                           in
                                        let _0_499 = prob_to_string env sub
                                           in
                                        FStar_Util.print2
                                          "Projecting %s\n\tsubprob=%s\n"
                                          _0_500 _0_499
                                    | uu____7331 -> ());
                                   (let wl =
                                      let _0_501 =
                                        Some
                                          (FStar_All.pipe_left Prims.fst
                                             (p_guard sub))
                                         in
                                      solve_prob orig _0_501 [TERM (u, proj)]
                                        wl
                                       in
                                    let _0_503 = solve env (attempt [sub] wl)
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_502  -> Some _0_502) _0_503))))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl =
          let uu____7360 = lhs  in
          match uu____7360 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____7383 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____7383 with
                | (xs,c) ->
                    (match (FStar_List.length xs) = (FStar_List.length ps)
                     with
                     | true  ->
                         Some
                           (let _0_504 = decompose env t2  in
                            (((uv, k_uv), xs, c), ps, _0_504))
                     | uu____7457 ->
                         let k_uv =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env k_uv
                            in
                         let rec elim k args =
                           let uu____7474 =
                             let _0_505 =
                               (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n
                                in
                             (_0_505, args)  in
                           match uu____7474 with
                           | (uu____7482,[]) ->
                               Some
                                 (let _0_506 = FStar_Syntax_Syntax.mk_Total k
                                     in
                                  ([], _0_506))
                           | (FStar_Syntax_Syntax.Tm_uvar _,_)
                             |(FStar_Syntax_Syntax.Tm_app _,_) ->
                               let uu____7500 =
                                 FStar_Syntax_Util.head_and_args k  in
                               (match uu____7500 with
                                | (uv,uv_args) ->
                                    let uu____7529 =
                                      (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n
                                       in
                                    (match uu____7529 with
                                     | FStar_Syntax_Syntax.Tm_uvar
                                         (uvar,uu____7534) ->
                                         let uu____7547 =
                                           pat_vars env [] uv_args  in
                                         (match uu____7547 with
                                          | None  -> None
                                          | Some scope ->
                                              let xs =
                                                FStar_All.pipe_right args
                                                  (FStar_List.map
                                                     (fun uu____7561  ->
                                                        let _0_510 =
                                                          let _0_509 =
                                                            Prims.fst
                                                              (let _0_508 =
                                                                 let _0_507 =
                                                                   FStar_Syntax_Util.type_u
                                                                    ()
                                                                    in
                                                                 FStar_All.pipe_right
                                                                   _0_507
                                                                   Prims.fst
                                                                  in
                                                               new_uvar
                                                                 k.FStar_Syntax_Syntax.pos
                                                                 scope _0_508)
                                                             in
                                                          FStar_Syntax_Syntax.new_bv
                                                            (Some
                                                               (k.FStar_Syntax_Syntax.pos))
                                                            _0_509
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Syntax.mk_binder
                                                          _0_510))
                                                 in
                                              let c =
                                                FStar_Syntax_Syntax.mk_Total
                                                  (Prims.fst
                                                     (let _0_512 =
                                                        let _0_511 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          _0_511 Prims.fst
                                                         in
                                                      new_uvar
                                                        k.FStar_Syntax_Syntax.pos
                                                        scope _0_512))
                                                 in
                                              let k' =
                                                FStar_Syntax_Util.arrow xs c
                                                 in
                                              let uv_sol =
                                                let _0_515 =
                                                  Some
                                                    (FStar_Util.Inl
                                                       (let _0_514 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            (let _0_513 =
                                                               FStar_Syntax_Util.type_u
                                                                 ()
                                                                in
                                                             FStar_All.pipe_right
                                                               _0_513
                                                               Prims.fst)
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.lcomp_of_comp
                                                          _0_514))
                                                   in
                                                FStar_Syntax_Util.abs scope
                                                  k' _0_515
                                                 in
                                              (FStar_Unionfind.change uvar
                                                 (FStar_Syntax_Syntax.Fixed
                                                    uv_sol);
                                               Some (xs, c)))
                                     | uu____7591 -> None))
                           | (FStar_Syntax_Syntax.Tm_arrow (xs,c),uu____7596)
                               ->
                               let n_args = FStar_List.length args  in
                               let n_xs = FStar_List.length xs  in
                               (match n_xs = n_args with
                                | true  ->
                                    let _0_517 =
                                      FStar_Syntax_Subst.open_comp xs c  in
                                    FStar_All.pipe_right _0_517
                                      (fun _0_516  -> Some _0_516)
                                | uu____7629 ->
                                    (match n_xs < n_args with
                                     | true  ->
                                         let uu____7638 =
                                           FStar_Util.first_N n_xs args  in
                                         (match uu____7638 with
                                          | (args,rest) ->
                                              let uu____7654 =
                                                FStar_Syntax_Subst.open_comp
                                                  xs c
                                                 in
                                              (match uu____7654 with
                                               | (xs,c) ->
                                                   let _0_518 =
                                                     elim
                                                       (FStar_Syntax_Util.comp_result
                                                          c) rest
                                                      in
                                                   FStar_Util.bind_opt _0_518
                                                     (fun uu____7669  ->
                                                        match uu____7669 with
                                                        | (xs',c) ->
                                                            Some
                                                              ((FStar_List.append
                                                                  xs xs'), c))))
                                     | uu____7690 ->
                                         let uu____7691 =
                                           FStar_Util.first_N n_args xs  in
                                         (match uu____7691 with
                                          | (xs,rest) ->
                                              let t =
                                                (FStar_Syntax_Syntax.mk
                                                   (FStar_Syntax_Syntax.Tm_arrow
                                                      (rest, c))) None
                                                  k.FStar_Syntax_Syntax.pos
                                                 in
                                              let _0_521 =
                                                let _0_519 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    t
                                                   in
                                                FStar_Syntax_Subst.open_comp
                                                  xs _0_519
                                                 in
                                              FStar_All.pipe_right _0_521
                                                (fun _0_520  -> Some _0_520))))
                           | uu____7744 ->
                               failwith
                                 (let _0_524 =
                                    FStar_Syntax_Print.uvar_to_string uv  in
                                  let _0_523 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  let _0_522 =
                                    FStar_Syntax_Print.term_to_string k_uv
                                     in
                                  FStar_Util.format3
                                    "Impossible: ill-typed application %s : %s\n\t%s"
                                    _0_524 _0_523 _0_522)
                            in
                         let _0_526 = elim k_uv ps  in
                         FStar_Util.bind_opt _0_526
                           (fun uu____7778  ->
                              match uu____7778 with
                              | (xs,c) ->
                                  Some
                                    (let _0_525 = decompose env t2  in
                                     (((uv, k_uv), xs, c), ps, _0_525))))
                 in
              let rec imitate_or_project n stopt i =
                match (i >= n) || (FStar_Option.isNone stopt) with
                | true  ->
                    giveup env
                      "flex-rigid case failed all backtracking attempts" orig
                | uu____7861 ->
                    let st = FStar_Option.get stopt  in
                    let tx = FStar_Unionfind.new_transaction ()  in
                    (match i = (~- (Prims.parse_int "1")) with
                     | true  ->
                         let uu____7864 = imitate orig env wl st  in
                         (match uu____7864 with
                          | Failed uu____7869 ->
                              (FStar_Unionfind.rollback tx;
                               imitate_or_project n stopt
                                 (i + (Prims.parse_int "1")))
                          | sol -> sol)
                     | uu____7874 ->
                         let uu____7875 = project orig env wl i st  in
                         (match uu____7875 with
                          | None |Some (Failed _) ->
                              (FStar_Unionfind.rollback tx;
                               imitate_or_project n stopt
                                 (i + (Prims.parse_int "1")))
                          | Some sol -> sol))
                 in
              let check_head fvs1 t2 =
                let uu____7893 = FStar_Syntax_Util.head_and_args t2  in
                match uu____7893 with
                | (hd,uu____7904) ->
                    (match hd.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____7922 ->
                         let fvs_hd = FStar_Syntax_Free.names hd  in
                         let uu____7925 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         (match uu____7925 with
                          | true  -> true
                          | uu____7926 ->
                              ((let uu____7928 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                match uu____7928 with
                                | true  ->
                                    let _0_527 = names_to_string fvs_hd  in
                                    FStar_Util.print1 "Free variables are %s"
                                      _0_527
                                | uu____7929 -> ());
                               false)))
                 in
              let imitate_ok t2 =
                let fvs_hd =
                  let _0_529 =
                    let _0_528 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right _0_528 Prims.fst  in
                  FStar_All.pipe_right _0_529 FStar_Syntax_Free.names  in
                let uu____7957 = FStar_Util.set_is_empty fvs_hd  in
                match uu____7957 with
                | true  -> ~- (Prims.parse_int "1")
                | uu____7958 -> (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t1 = sn env t1  in
                   let t2 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t1  in
                   let fvs2 = FStar_Syntax_Free.names t2  in
                   let uu____7966 = occurs_check env wl (uv, k_uv) t2  in
                   (match uu____7966 with
                    | (occurs_ok,msg) ->
                        (match Prims.op_Negation occurs_ok with
                         | true  ->
                             let _0_531 =
                               let _0_530 = FStar_Option.get msg  in
                               Prims.strcat "occurs-check failed: " _0_530
                                in
                             giveup_or_defer orig _0_531
                         | uu____7974 ->
                             let uu____7975 =
                               FStar_Util.set_is_subset_of fvs2 fvs1  in
                             (match uu____7975 with
                              | true  ->
                                  let uu____7976 =
                                    ((Prims.op_Negation patterns_only) &&
                                       (FStar_Syntax_Util.is_function_typ t2))
                                      &&
                                      ((p_rel orig) <>
                                         FStar_TypeChecker_Common.EQ)
                                     in
                                  (match uu____7976 with
                                   | true  ->
                                       let _0_532 = subterms args_lhs  in
                                       imitate' orig env wl _0_532
                                   | uu____7977 ->
                                       ((let uu____7979 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other "Rel")
                                            in
                                         match uu____7979 with
                                         | true  ->
                                             let _0_535 =
                                               FStar_Syntax_Print.term_to_string
                                                 t1
                                                in
                                             let _0_534 =
                                               names_to_string fvs1  in
                                             let _0_533 =
                                               names_to_string fvs2  in
                                             FStar_Util.print3
                                               "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                               _0_535 _0_534 _0_533
                                         | uu____7980 -> ());
                                        (let sol =
                                           match vars with
                                           | [] -> t2
                                           | uu____7984 ->
                                               let _0_536 =
                                                 sn_binders env vars  in
                                               u_abs k_uv _0_536 t2
                                            in
                                         let wl =
                                           solve_prob orig None
                                             [TERM ((uv, k_uv), sol)] wl
                                            in
                                         solve env wl)))
                              | uu____7988 ->
                                  (match ((Prims.op_Negation patterns_only)
                                            && wl.defer_ok)
                                           &&
                                           ((p_rel orig) <>
                                              FStar_TypeChecker_Common.EQ)
                                   with
                                   | true  ->
                                       solve env
                                         (defer
                                            "flex pattern/rigid: occurs or freevar check"
                                            orig wl)
                                   | uu____7989 ->
                                       let uu____7990 =
                                         (Prims.op_Negation patterns_only) &&
                                           (check_head fvs1 t2)
                                          in
                                       (match uu____7990 with
                                        | true  ->
                                            ((let uu____7992 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other "Rel")
                                                 in
                                              match uu____7992 with
                                              | true  ->
                                                  let _0_539 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t1
                                                     in
                                                  let _0_538 =
                                                    names_to_string fvs1  in
                                                  let _0_537 =
                                                    names_to_string fvs2  in
                                                  FStar_Util.print3
                                                    "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                                    _0_539 _0_538 _0_537
                                              | uu____7993 -> ());
                                             (let _0_540 = subterms args_lhs
                                                 in
                                              imitate_or_project
                                                (FStar_List.length args_lhs)
                                                _0_540
                                                (~- (Prims.parse_int "1"))))
                                        | uu____8001 ->
                                            giveup env
                                              "free-variable check failed on a non-redex"
                                              orig)))))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   (match wl.defer_ok with
                    | true  -> solve env (defer "not a pattern" orig wl)
                    | uu____8002 ->
                        let uu____8003 =
                          let _0_541 = FStar_Syntax_Free.names t1  in
                          check_head _0_541 t2  in
                        (match uu____8003 with
                         | true  ->
                             let im_ok = imitate_ok t2  in
                             ((let uu____8006 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "Rel")
                                  in
                               match uu____8006 with
                               | true  ->
                                   let _0_542 =
                                     FStar_Syntax_Print.term_to_string t1  in
                                   FStar_Util.print2
                                     "Not a pattern (%s) ... %s\n" _0_542
                                     (match im_ok < (Prims.parse_int "0")
                                      with
                                      | true  -> "imitating"
                                      | uu____8007 -> "projecting")
                               | uu____8008 -> ());
                              (let _0_543 = subterms args_lhs  in
                               imitate_or_project
                                 (FStar_List.length args_lhs) _0_543 im_ok))
                         | uu____8016 ->
                             giveup env "head-symbol is free" orig)))
           in
        let flex_flex orig lhs rhs =
          match wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          with
          | true  -> solve env (defer "flex-flex deferred" orig wl)
          | uu____8027 ->
              let force_quasi_pattern xs_opt uu____8049 =
                match uu____8049 with
                | (t,u,k,args) ->
                    let uu____8079 = FStar_Syntax_Util.arrow_formals k  in
                    (match uu____8079 with
                     | (all_formals,uu____8090) ->
                         let rec aux pat_args pattern_vars pattern_var_set
                           formals args =
                           match (formals, args) with
                           | ([],[]) ->
                               let pat_args =
                                 FStar_All.pipe_right
                                   (FStar_List.rev pat_args)
                                   (FStar_List.map
                                      (fun uu____8182  ->
                                         match uu____8182 with
                                         | (x,imp) ->
                                             let _0_544 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x
                                                in
                                             (_0_544, imp)))
                                  in
                               let pattern_vars = FStar_List.rev pattern_vars
                                  in
                               let kk =
                                 let uu____8196 = FStar_Syntax_Util.type_u ()
                                    in
                                 match uu____8196 with
                                 | (t,uu____8200) ->
                                     Prims.fst
                                       (new_uvar t.FStar_Syntax_Syntax.pos
                                          pattern_vars t)
                                  in
                               let uu____8201 =
                                 new_uvar t.FStar_Syntax_Syntax.pos
                                   pattern_vars kk
                                  in
                               (match uu____8201 with
                                | (t',tm_u1) ->
                                    let uu____8208 = destruct_flex_t t'  in
                                    (match uu____8208 with
                                     | (uu____8228,u1,k1,uu____8231) ->
                                         let sol =
                                           TERM
                                             (let _0_545 =
                                                u_abs k all_formals t'  in
                                              ((u, k), _0_545))
                                            in
                                         let t_app =
                                           (FStar_Syntax_Syntax.mk_Tm_app
                                              tm_u1 pat_args) None
                                             t.FStar_Syntax_Syntax.pos
                                            in
                                         (sol, (t_app, u1, k1, pat_args))))
                           | (formal::formals,hd::tl) ->
                               let uu____8318 = pat_var_opt env pat_args hd
                                  in
                               (match uu____8318 with
                                | None  ->
                                    aux pat_args pattern_vars pattern_var_set
                                      formals tl
                                | Some y ->
                                    let maybe_pat =
                                      match xs_opt with
                                      | None  -> true
                                      | Some xs ->
                                          FStar_All.pipe_right xs
                                            (FStar_Util.for_some
                                               (fun uu____8347  ->
                                                  match uu____8347 with
                                                  | (x,uu____8351) ->
                                                      FStar_Syntax_Syntax.bv_eq
                                                        x (Prims.fst y)))
                                       in
                                    (match Prims.op_Negation maybe_pat with
                                     | true  ->
                                         aux pat_args pattern_vars
                                           pattern_var_set formals tl
                                     | uu____8354 ->
                                         let fvs =
                                           FStar_Syntax_Free.names
                                             (Prims.fst y).FStar_Syntax_Syntax.sort
                                            in
                                         let uu____8357 =
                                           Prims.op_Negation
                                             (FStar_Util.set_is_subset_of fvs
                                                pattern_var_set)
                                            in
                                         (match uu____8357 with
                                          | true  ->
                                              aux pat_args pattern_vars
                                                pattern_var_set formals tl
                                          | uu____8360 ->
                                              let _0_546 =
                                                FStar_Util.set_add
                                                  (Prims.fst formal)
                                                  pattern_var_set
                                                 in
                                              aux (y :: pat_args) (formal ::
                                                pattern_vars) _0_546 formals
                                                tl)))
                           | uu____8365 -> failwith "Impossible"  in
                         let _0_547 = FStar_Syntax_Syntax.new_bv_set ()  in
                         aux [] [] _0_547 all_formals args)
                 in
              let solve_both_pats wl uu____8422 uu____8423 r =
                match (uu____8422, uu____8423) with
                | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                    let uu____8577 =
                      (FStar_Unionfind.equivalent u1 u2) &&
                        (binders_eq xs ys)
                       in
                    (match uu____8577 with
                     | true  ->
                         let _0_548 = solve_prob orig None [] wl  in
                         solve env _0_548
                     | uu____8581 ->
                         let xs = sn_binders env xs  in
                         let ys = sn_binders env ys  in
                         let zs = intersect_vars xs ys  in
                         ((let uu____8595 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           match uu____8595 with
                           | true  ->
                               let _0_553 =
                                 FStar_Syntax_Print.binders_to_string ", " xs
                                  in
                               let _0_552 =
                                 FStar_Syntax_Print.binders_to_string ", " ys
                                  in
                               let _0_551 =
                                 FStar_Syntax_Print.binders_to_string ", " zs
                                  in
                               let _0_550 =
                                 FStar_Syntax_Print.term_to_string k1  in
                               let _0_549 =
                                 FStar_Syntax_Print.term_to_string k2  in
                               FStar_Util.print5
                                 "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                                 _0_553 _0_552 _0_551 _0_550 _0_549
                           | uu____8596 -> ());
                          (let subst_k k xs args =
                             let xs_len = FStar_List.length xs  in
                             let args_len = FStar_List.length args  in
                             match xs_len = args_len with
                             | true  ->
                                 let _0_554 =
                                   FStar_Syntax_Util.subst_of_list xs args
                                    in
                                 FStar_Syntax_Subst.subst _0_554 k
                             | uu____8637 ->
                                 (match args_len < xs_len with
                                  | true  ->
                                      let uu____8643 =
                                        FStar_Util.first_N args_len xs  in
                                      (match uu____8643 with
                                       | (xs,xs_rest) ->
                                           let k =
                                             let _0_555 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 k
                                                in
                                             FStar_Syntax_Util.arrow xs_rest
                                               _0_555
                                              in
                                           let _0_556 =
                                             FStar_Syntax_Util.subst_of_list
                                               xs args
                                              in
                                           FStar_Syntax_Subst.subst _0_556 k)
                                  | uu____8673 ->
                                      failwith
                                        (let _0_559 =
                                           FStar_Syntax_Print.term_to_string
                                             k
                                            in
                                         let _0_558 =
                                           FStar_Syntax_Print.binders_to_string
                                             ", " xs
                                            in
                                         let _0_557 =
                                           FStar_Syntax_Print.args_to_string
                                             args
                                            in
                                         FStar_Util.format3
                                           "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                           _0_559 _0_558 _0_557))
                              in
                           let uu____8674 =
                             let uu____8680 =
                               FStar_Syntax_Util.arrow_formals
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k1)
                                in
                             match uu____8680 with
                             | (bs,k1') ->
                                 let uu____8705 =
                                   FStar_Syntax_Util.arrow_formals
                                     (FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Normalize.Beta]
                                        env k2)
                                    in
                                 (match uu____8705 with
                                  | (cs,k2') ->
                                      let k1'_xs = subst_k k1' bs args1  in
                                      let k2'_ys = subst_k k2' cs args2  in
                                      let sub_prob =
                                        let _0_561 =
                                          mk_problem (p_scope orig) orig
                                            k1'_xs
                                            FStar_TypeChecker_Common.EQ
                                            k2'_ys None "flex-flex kinding"
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_560  ->
                                             FStar_TypeChecker_Common.TProb
                                               _0_560) _0_561
                                         in
                                      let uu____8735 =
                                        let _0_563 =
                                          (FStar_Syntax_Subst.compress k1').FStar_Syntax_Syntax.n
                                           in
                                        let _0_562 =
                                          (FStar_Syntax_Subst.compress k2').FStar_Syntax_Syntax.n
                                           in
                                        (_0_563, _0_562)  in
                                      (match uu____8735 with
                                       | (FStar_Syntax_Syntax.Tm_type
                                          uu____8743,uu____8744) ->
                                           (k1', [sub_prob])
                                       | (uu____8748,FStar_Syntax_Syntax.Tm_type
                                          uu____8749) -> (k2', [sub_prob])
                                       | uu____8753 ->
                                           let uu____8756 =
                                             FStar_Syntax_Util.type_u ()  in
                                           (match uu____8756 with
                                            | (t,uu____8765) ->
                                                let uu____8766 =
                                                  new_uvar r zs t  in
                                                (match uu____8766 with
                                                 | (k_zs,uu____8775) ->
                                                     let kprob =
                                                       let _0_565 =
                                                         mk_problem
                                                           (p_scope orig)
                                                           orig k1'_xs
                                                           FStar_TypeChecker_Common.EQ
                                                           k_zs None
                                                           "flex-flex kinding"
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_564  ->
                                                            FStar_TypeChecker_Common.TProb
                                                              _0_564) _0_565
                                                        in
                                                     (k_zs,
                                                       [sub_prob; kprob])))))
                              in
                           match uu____8674 with
                           | (k_u',sub_probs) ->
                               let uu____8788 =
                                 let _0_571 =
                                   let _0_566 = new_uvar r zs k_u'  in
                                   FStar_All.pipe_left Prims.fst _0_566  in
                                 let _0_570 =
                                   let _0_567 =
                                     FStar_Syntax_Syntax.mk_Total k_u'  in
                                   FStar_Syntax_Util.arrow xs _0_567  in
                                 let _0_569 =
                                   let _0_568 =
                                     FStar_Syntax_Syntax.mk_Total k_u'  in
                                   FStar_Syntax_Util.arrow ys _0_568  in
                                 (_0_571, _0_570, _0_569)  in
                               (match uu____8788 with
                                | (u_zs,knew1,knew2) ->
                                    let sub1 = u_abs knew1 xs u_zs  in
                                    let uu____8814 =
                                      occurs_check env wl (u1, k1) sub1  in
                                    (match uu____8814 with
                                     | (occurs_ok,msg) ->
                                         (match Prims.op_Negation occurs_ok
                                          with
                                          | true  ->
                                              giveup_or_defer orig
                                                "flex-flex: failed occcurs check"
                                          | uu____8826 ->
                                              let sol1 =
                                                TERM ((u1, k1), sub1)  in
                                              let uu____8838 =
                                                FStar_Unionfind.equivalent u1
                                                  u2
                                                 in
                                              (match uu____8838 with
                                               | true  ->
                                                   let wl =
                                                     solve_prob orig None
                                                       [sol1] wl
                                                      in
                                                   solve env wl
                                               | uu____8843 ->
                                                   let sub2 =
                                                     u_abs knew2 ys u_zs  in
                                                   let uu____8845 =
                                                     occurs_check env wl
                                                       (u2, k2) sub2
                                                      in
                                                   (match uu____8845 with
                                                    | (occurs_ok,msg) ->
                                                        (match Prims.op_Negation
                                                                 occurs_ok
                                                         with
                                                         | true  ->
                                                             giveup_or_defer
                                                               orig
                                                               "flex-flex: failed occurs check"
                                                         | uu____8857 ->
                                                             let sol2 =
                                                               TERM
                                                                 ((u2, k2),
                                                                   sub2)
                                                                in
                                                             let wl =
                                                               solve_prob
                                                                 orig None
                                                                 [sol1; sol2]
                                                                 wl
                                                                in
                                                             solve env
                                                               (attempt
                                                                  sub_probs
                                                                  wl))))))))))
                 in
              let solve_one_pat uu____8897 uu____8898 =
                match (uu____8897, uu____8898) with
                | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                    ((let uu____9002 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      match uu____9002 with
                      | true  ->
                          let _0_573 = FStar_Syntax_Print.term_to_string t1
                             in
                          let _0_572 = FStar_Syntax_Print.term_to_string t2
                             in
                          FStar_Util.print2
                            "Trying flex-flex one pattern (%s) with %s\n"
                            _0_573 _0_572
                      | uu____9003 -> ());
                     (let uu____9004 = FStar_Unionfind.equivalent u1 u2  in
                      match uu____9004 with
                      | true  ->
                          let sub_probs =
                            FStar_List.map2
                              (fun uu____9014  ->
                                 fun uu____9015  ->
                                   match (uu____9014, uu____9015) with
                                   | ((a,uu____9025),(t2,uu____9027)) ->
                                       let _0_576 =
                                         let _0_574 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         mk_problem (p_scope orig) orig
                                           _0_574 FStar_TypeChecker_Common.EQ
                                           t2 None "flex-flex index"
                                          in
                                       FStar_All.pipe_right _0_576
                                         (fun _0_575  ->
                                            FStar_TypeChecker_Common.TProb
                                              _0_575)) xs args2
                             in
                          let guard =
                            FStar_Syntax_Util.mk_conj_l
                              (FStar_List.map
                                 (fun p  ->
                                    FStar_All.pipe_right (p_guard p)
                                      Prims.fst) sub_probs)
                             in
                          let wl = solve_prob orig (Some guard) [] wl  in
                          solve env (attempt sub_probs wl)
                      | uu____9039 ->
                          let t2 = sn env t2  in
                          let rhs_vars = FStar_Syntax_Free.names t2  in
                          let uu____9043 = occurs_check env wl (u1, k1) t2
                             in
                          (match uu____9043 with
                           | (occurs_ok,uu____9052) ->
                               let lhs_vars =
                                 FStar_Syntax_Free.names_of_binders xs  in
                               let uu____9057 =
                                 occurs_ok &&
                                   (FStar_Util.set_is_subset_of rhs_vars
                                      lhs_vars)
                                  in
                               (match uu____9057 with
                                | true  ->
                                    let sol =
                                      TERM
                                        (let _0_577 = u_abs k1 xs t2  in
                                         ((u1, k1), _0_577))
                                       in
                                    let wl = solve_prob orig None [sol] wl
                                       in
                                    solve env wl
                                | uu____9070 ->
                                    let uu____9071 =
                                      occurs_ok &&
                                        (FStar_All.pipe_left
                                           Prims.op_Negation wl.defer_ok)
                                       in
                                    (match uu____9071 with
                                     | true  ->
                                         let uu____9072 =
                                           force_quasi_pattern (Some xs)
                                             (t2, u2, k2, args2)
                                            in
                                         (match uu____9072 with
                                          | (sol,(uu____9086,u2,k2,ys)) ->
                                              let wl =
                                                extend_solution (p_pid orig)
                                                  [sol] wl
                                                 in
                                              ((let uu____9096 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "QuasiPattern")
                                                   in
                                                match uu____9096 with
                                                | true  ->
                                                    let _0_578 =
                                                      uvi_to_string env sol
                                                       in
                                                    FStar_Util.print1
                                                      "flex-flex quasi pattern (2): %s\n"
                                                      _0_578
                                                | uu____9097 -> ());
                                               (match orig with
                                                | FStar_TypeChecker_Common.TProb
                                                    p -> solve_t env p wl
                                                | uu____9101 ->
                                                    giveup env "impossible"
                                                      orig)))
                                     | uu____9102 ->
                                         giveup_or_defer orig
                                           "flex-flex constraint")))))
                 in
              let uu____9103 = lhs  in
              (match uu____9103 with
               | (t1,u1,k1,args1) ->
                   let uu____9108 = rhs  in
                   (match uu____9108 with
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
                         | uu____9134 ->
                             (match wl.defer_ok with
                              | true  ->
                                  giveup_or_defer orig
                                    "flex-flex: neither side is a pattern"
                              | uu____9139 ->
                                  let uu____9140 =
                                    force_quasi_pattern None
                                      (t1, u1, k1, args1)
                                     in
                                  (match uu____9140 with
                                   | (sol,uu____9147) ->
                                       let wl =
                                         extend_solution (p_pid orig) 
                                           [sol] wl
                                          in
                                       ((let uu____9150 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "QuasiPattern")
                                            in
                                         match uu____9150 with
                                         | true  ->
                                             let _0_579 =
                                               uvi_to_string env sol  in
                                             FStar_Util.print1
                                               "flex-flex quasi pattern (1): %s\n"
                                               _0_579
                                         | uu____9151 -> ());
                                        (match orig with
                                         | FStar_TypeChecker_Common.TProb p
                                             -> solve_t env p wl
                                         | uu____9155 ->
                                             giveup env "impossible" orig)))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____9157 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        match uu____9157 with
        | true  ->
            let _0_580 = solve_prob orig None [] wl  in solve env _0_580
        | uu____9158 ->
            let t1 = problem.FStar_TypeChecker_Common.lhs  in
            let t2 = problem.FStar_TypeChecker_Common.rhs  in
            let uu____9161 = FStar_Util.physical_equality t1 t2  in
            (match uu____9161 with
             | true  ->
                 let _0_581 = solve_prob orig None [] wl  in solve env _0_581
             | uu____9162 ->
                 ((let uu____9164 =
                     FStar_TypeChecker_Env.debug env
                       (FStar_Options.Other "RelCheck")
                      in
                   match uu____9164 with
                   | true  ->
                       let _0_582 =
                         FStar_Util.string_of_int
                           problem.FStar_TypeChecker_Common.pid
                          in
                       FStar_Util.print1 "Attempting %s\n" _0_582
                   | uu____9165 -> ());
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   match ((t1.FStar_Syntax_Syntax.n),
                           (t2.FStar_Syntax_Syntax.n))
                   with
                   | (FStar_Syntax_Syntax.Tm_bvar _,_)
                     |(_,FStar_Syntax_Syntax.Tm_bvar _) ->
                       failwith
                         "Only locally nameless! We should never see a de Bruijn variable"
                   | (FStar_Syntax_Syntax.Tm_type
                      u1,FStar_Syntax_Syntax.Tm_type u2) ->
                       solve_one_universe_eq env orig u1 u2 wl
                   | (FStar_Syntax_Syntax.Tm_arrow
                      (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                       let mk_c c uu___124_9210 =
                         match uu___124_9210 with
                         | [] -> c
                         | bs ->
                             FStar_Syntax_Syntax.mk_Total
                               ((FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_arrow (bs, c)))
                                  None c.FStar_Syntax_Syntax.pos)
                          in
                       let uu____9245 =
                         match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))
                          in
                       (match uu____9245 with
                        | ((bs1,c1),(bs2,c2)) ->
                            solve_binders env bs1 bs2 orig wl
                              (fun scope  ->
                                 fun env  ->
                                   fun subst  ->
                                     let c1 =
                                       FStar_Syntax_Subst.subst_comp subst c1
                                        in
                                     let c2 =
                                       FStar_Syntax_Subst.subst_comp subst c2
                                        in
                                     let rel =
                                       let uu____9331 =
                                         FStar_Options.use_eq_at_higher_order
                                           ()
                                          in
                                       match uu____9331 with
                                       | true  -> FStar_TypeChecker_Common.EQ
                                       | uu____9332 ->
                                           problem.FStar_TypeChecker_Common.relation
                                        in
                                     let _0_584 =
                                       mk_problem scope orig c1 rel c2 None
                                         "function co-domain"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_583  ->
                                          FStar_TypeChecker_Common.CProb
                                            _0_583) _0_584))
                   | (FStar_Syntax_Syntax.Tm_abs
                      (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                      (bs2,tbody2,lopt2)) ->
                       let mk_t t l uu___125_9407 =
                         match uu___125_9407 with
                         | [] -> t
                         | bs ->
                             (FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                               t.FStar_Syntax_Syntax.pos
                          in
                       let uu____9446 =
                         match_num_binders (bs1, (mk_t tbody1 lopt1))
                           (bs2, (mk_t tbody2 lopt2))
                          in
                       (match uu____9446 with
                        | ((bs1,tbody1),(bs2,tbody2)) ->
                            solve_binders env bs1 bs2 orig wl
                              (fun scope  ->
                                 fun env  ->
                                   fun subst  ->
                                     let _0_588 =
                                       let _0_587 =
                                         FStar_Syntax_Subst.subst subst
                                           tbody1
                                          in
                                       let _0_586 =
                                         FStar_Syntax_Subst.subst subst
                                           tbody2
                                          in
                                       mk_problem scope orig _0_587
                                         problem.FStar_TypeChecker_Common.relation
                                         _0_586 None "lambda co-domain"
                                        in
                                     FStar_All.pipe_left
                                       (fun _0_585  ->
                                          FStar_TypeChecker_Common.TProb
                                            _0_585) _0_588))
                   | (FStar_Syntax_Syntax.Tm_abs _,_)
                     |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                       let is_abs t =
                         match t.FStar_Syntax_Syntax.n with
                         | FStar_Syntax_Syntax.Tm_abs uu____9543 -> true
                         | uu____9558 -> false  in
                       let maybe_eta t =
                         match is_abs t with
                         | true  -> FStar_Util.Inl t
                         | uu____9577 ->
                             let t =
                               FStar_TypeChecker_Normalize.eta_expand
                                 wl.tcenv t
                                in
                             (match is_abs t with
                              | true  -> FStar_Util.Inl t
                              | uu____9583 -> FStar_Util.Inr t)
                          in
                       let uu____9586 =
                         let _0_590 = maybe_eta t1  in
                         let _0_589 = maybe_eta t2  in (_0_590, _0_589)  in
                       (match uu____9586 with
                        | (FStar_Util.Inl t1,FStar_Util.Inl t2) ->
                            solve_t env
                              (let uu___153_9623 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___153_9623.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t1;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___153_9623.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t2;
                                 FStar_TypeChecker_Common.element =
                                   (uu___153_9623.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___153_9623.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.scope =
                                   (uu___153_9623.FStar_TypeChecker_Common.scope);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___153_9623.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___153_9623.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___153_9623.FStar_TypeChecker_Common.rank)
                               }) wl
                        | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                          |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                            let uu____9656 =
                              (is_flex not_abs) &&
                                ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                               in
                            (match uu____9656 with
                             | true  ->
                                 let _0_591 =
                                   destruct_flex_pattern env not_abs  in
                                 solve_t_flex_rigid true orig _0_591 t_abs wl
                             | uu____9657 ->
                                 giveup env
                                   "head tag mismatch: RHS is an abstraction"
                                   orig)
                        | uu____9658 ->
                            failwith
                              "Impossible: at least one side is an abstraction")
                   | (FStar_Syntax_Syntax.Tm_refine
                      uu____9669,FStar_Syntax_Syntax.Tm_refine uu____9670) ->
                       let uu____9679 = as_refinement env wl t1  in
                       (match uu____9679 with
                        | (x1,phi1) ->
                            let uu____9684 = as_refinement env wl t2  in
                            (match uu____9684 with
                             | (x2,phi2) ->
                                 let base_prob =
                                   let _0_593 =
                                     mk_problem (p_scope orig) orig
                                       x1.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x2.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   FStar_All.pipe_left
                                     (fun _0_592  ->
                                        FStar_TypeChecker_Common.TProb _0_592)
                                     _0_593
                                    in
                                 let x1 = FStar_Syntax_Syntax.freshen_bv x1
                                    in
                                 let subst =
                                   [FStar_Syntax_Syntax.DB
                                      ((Prims.parse_int "0"), x1)]
                                    in
                                 let phi1 =
                                   FStar_Syntax_Subst.subst subst phi1  in
                                 let phi2 =
                                   FStar_Syntax_Subst.subst subst phi2  in
                                 let env =
                                   FStar_TypeChecker_Env.push_bv env x1  in
                                 let mk_imp imp phi1 phi2 =
                                   let _0_594 = imp phi1 phi2  in
                                   FStar_All.pipe_right _0_594
                                     (guard_on_element problem x1)
                                    in
                                 let fallback uu____9723 =
                                   let impl =
                                     match problem.FStar_TypeChecker_Common.relation
                                             = FStar_TypeChecker_Common.EQ
                                     with
                                     | true  ->
                                         mk_imp FStar_Syntax_Util.mk_iff phi1
                                           phi2
                                     | uu____9725 ->
                                         mk_imp FStar_Syntax_Util.mk_imp phi1
                                           phi2
                                      in
                                   let guard =
                                     let _0_595 =
                                       FStar_All.pipe_right
                                         (p_guard base_prob) Prims.fst
                                        in
                                     FStar_Syntax_Util.mk_conj _0_595 impl
                                      in
                                   let wl =
                                     solve_prob orig (Some guard) [] wl  in
                                   solve env (attempt [base_prob] wl)  in
                                 (match problem.FStar_TypeChecker_Common.relation
                                          = FStar_TypeChecker_Common.EQ
                                  with
                                  | true  ->
                                      let ref_prob =
                                        let _0_599 =
                                          let _0_598 =
                                            let _0_597 =
                                              FStar_Syntax_Syntax.mk_binder
                                                x1
                                               in
                                            _0_597 :: (p_scope orig)  in
                                          mk_problem _0_598 orig phi1
                                            FStar_TypeChecker_Common.EQ phi2
                                            None "refinement formula"
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_596  ->
                                             FStar_TypeChecker_Common.TProb
                                               _0_596) _0_599
                                         in
                                      let uu____9737 =
                                        solve env
                                          (let uu___154_9738 = wl  in
                                           {
                                             attempting = [ref_prob];
                                             wl_deferred = [];
                                             ctr = (uu___154_9738.ctr);
                                             defer_ok = false;
                                             smt_ok = (uu___154_9738.smt_ok);
                                             tcenv = (uu___154_9738.tcenv)
                                           })
                                         in
                                      (match uu____9737 with
                                       | Failed uu____9742 -> fallback ()
                                       | Success uu____9745 ->
                                           let guard =
                                             let _0_602 =
                                               FStar_All.pipe_right
                                                 (p_guard base_prob)
                                                 Prims.fst
                                                in
                                             let _0_601 =
                                               let _0_600 =
                                                 FStar_All.pipe_right
                                                   (p_guard ref_prob)
                                                   Prims.fst
                                                  in
                                               FStar_All.pipe_right _0_600
                                                 (guard_on_element problem x1)
                                                in
                                             FStar_Syntax_Util.mk_conj _0_602
                                               _0_601
                                              in
                                           let wl =
                                             solve_prob orig (Some guard) []
                                               wl
                                              in
                                           let wl =
                                             let uu___155_9757 = wl  in
                                             {
                                               attempting =
                                                 (uu___155_9757.attempting);
                                               wl_deferred =
                                                 (uu___155_9757.wl_deferred);
                                               ctr =
                                                 (wl.ctr +
                                                    (Prims.parse_int "1"));
                                               defer_ok =
                                                 (uu___155_9757.defer_ok);
                                               smt_ok =
                                                 (uu___155_9757.smt_ok);
                                               tcenv = (uu___155_9757.tcenv)
                                             }  in
                                           solve env (attempt [base_prob] wl))
                                  | uu____9758 -> fallback ())))
                   | (FStar_Syntax_Syntax.Tm_uvar
                      _,FStar_Syntax_Syntax.Tm_uvar _)
                     |(FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_uvar
                       _)
                      |(FStar_Syntax_Syntax.Tm_uvar
                        _,FStar_Syntax_Syntax.Tm_app
                        ({
                           FStar_Syntax_Syntax.n =
                             FStar_Syntax_Syntax.Tm_uvar _;
                           FStar_Syntax_Syntax.tk = _;
                           FStar_Syntax_Syntax.pos = _;
                           FStar_Syntax_Syntax.vars = _;_},_))
                       |(FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_uvar _;
                            FStar_Syntax_Syntax.tk = _;
                            FStar_Syntax_Syntax.pos = _;
                            FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_uvar _;
                            FStar_Syntax_Syntax.tk = _;
                            FStar_Syntax_Syntax.pos = _;
                            FStar_Syntax_Syntax.vars = _;_},_))
                       ->
                       let _0_604 = destruct_flex_t t1  in
                       let _0_603 = destruct_flex_t t2  in
                       flex_flex orig _0_604 _0_603
                   | (FStar_Syntax_Syntax.Tm_uvar _,_)
                     |(FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_),_)
                       when
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ
                       ->
                       let _0_605 = destruct_flex_pattern env t1  in
                       solve_t_flex_rigid false orig _0_605 t2 wl
                   | (_,FStar_Syntax_Syntax.Tm_uvar _)
                     |(_,FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_))
                       when
                       problem.FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ
                       -> solve_t env (invert problem) wl
                   | (FStar_Syntax_Syntax.Tm_uvar
                      _,FStar_Syntax_Syntax.Tm_type _)
                     |(FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_type
                       _)
                      |(FStar_Syntax_Syntax.Tm_uvar
                        _,FStar_Syntax_Syntax.Tm_arrow _)
                       |(FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_uvar _;
                            FStar_Syntax_Syntax.tk = _;
                            FStar_Syntax_Syntax.pos = _;
                            FStar_Syntax_Syntax.vars = _;_},_),FStar_Syntax_Syntax.Tm_arrow
                         _)
                       ->
                       solve_t' env
                         (let uu___156_9871 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___156_9871.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs =
                              (uu___156_9871.FStar_TypeChecker_Common.lhs);
                            FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ;
                            FStar_TypeChecker_Common.rhs =
                              (uu___156_9871.FStar_TypeChecker_Common.rhs);
                            FStar_TypeChecker_Common.element =
                              (uu___156_9871.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___156_9871.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___156_9871.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___156_9871.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___156_9871.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___156_9871.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Syntax_Syntax.Tm_uvar _,_)
                     |(FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_),_)
                       ->
                       (match wl.defer_ok with
                        | true  ->
                            solve env
                              (defer "flex-rigid subtyping deferred" orig wl)
                        | uu____9887 ->
                            let new_rel =
                              problem.FStar_TypeChecker_Common.relation  in
                            let uu____9889 =
                              let _0_606 = is_top_level_prob orig  in
                              FStar_All.pipe_left Prims.op_Negation _0_606
                               in
                            (match uu____9889 with
                             | true  ->
                                 let _0_609 =
                                   FStar_All.pipe_left
                                     (fun _0_607  ->
                                        FStar_TypeChecker_Common.TProb _0_607)
                                     (let uu___157_9892 = problem  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___157_9892.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___157_9892.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          new_rel;
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___157_9892.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___157_9892.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___157_9892.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___157_9892.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___157_9892.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___157_9892.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___157_9892.FStar_TypeChecker_Common.rank)
                                      })
                                    in
                                 let _0_608 = destruct_flex_pattern env t1
                                    in
                                 solve_t_flex_rigid false _0_609 _0_608 t2 wl
                             | uu____9893 ->
                                 let uu____9894 =
                                   base_and_refinement env wl t2  in
                                 (match uu____9894 with
                                  | (t_base,ref_opt) ->
                                      (match ref_opt with
                                       | None  ->
                                           let _0_612 =
                                             FStar_All.pipe_left
                                               (fun _0_610  ->
                                                  FStar_TypeChecker_Common.TProb
                                                    _0_610)
                                               (let uu___158_9926 = problem
                                                   in
                                                {
                                                  FStar_TypeChecker_Common.pid
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.pid);
                                                  FStar_TypeChecker_Common.lhs
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.lhs);
                                                  FStar_TypeChecker_Common.relation
                                                    = new_rel;
                                                  FStar_TypeChecker_Common.rhs
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.rhs);
                                                  FStar_TypeChecker_Common.element
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.element);
                                                  FStar_TypeChecker_Common.logical_guard
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.logical_guard);
                                                  FStar_TypeChecker_Common.scope
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.scope);
                                                  FStar_TypeChecker_Common.reason
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.reason);
                                                  FStar_TypeChecker_Common.loc
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.loc);
                                                  FStar_TypeChecker_Common.rank
                                                    =
                                                    (uu___158_9926.FStar_TypeChecker_Common.rank)
                                                })
                                              in
                                           let _0_611 =
                                             destruct_flex_pattern env t1  in
                                           solve_t_flex_rigid false _0_612
                                             _0_611 t_base wl
                                       | Some (y,phi) ->
                                           let y' =
                                             let uu___159_9938 = y  in
                                             {
                                               FStar_Syntax_Syntax.ppname =
                                                 (uu___159_9938.FStar_Syntax_Syntax.ppname);
                                               FStar_Syntax_Syntax.index =
                                                 (uu___159_9938.FStar_Syntax_Syntax.index);
                                               FStar_Syntax_Syntax.sort = t1
                                             }  in
                                           let impl =
                                             guard_on_element problem y' phi
                                              in
                                           let base_prob =
                                             let _0_614 =
                                               mk_problem
                                                 problem.FStar_TypeChecker_Common.scope
                                                 orig t1 new_rel
                                                 y.FStar_Syntax_Syntax.sort
                                                 problem.FStar_TypeChecker_Common.element
                                                 "flex-rigid: base type"
                                                in
                                             FStar_All.pipe_left
                                               (fun _0_613  ->
                                                  FStar_TypeChecker_Common.TProb
                                                    _0_613) _0_614
                                              in
                                           let guard =
                                             let _0_615 =
                                               FStar_All.pipe_right
                                                 (p_guard base_prob)
                                                 Prims.fst
                                                in
                                             FStar_Syntax_Util.mk_conj _0_615
                                               impl
                                              in
                                           let wl =
                                             solve_prob orig (Some guard) []
                                               wl
                                              in
                                           solve env (attempt [base_prob] wl)))))
                   | (_,FStar_Syntax_Syntax.Tm_uvar _)
                     |(_,FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                            _;
                          FStar_Syntax_Syntax.tk = _;
                          FStar_Syntax_Syntax.pos = _;
                          FStar_Syntax_Syntax.vars = _;_},_))
                       ->
                       (match wl.defer_ok with
                        | true  ->
                            solve env
                              (defer "rigid-flex subtyping deferred" orig wl)
                        | uu____9966 ->
                            let uu____9967 = base_and_refinement env wl t1
                               in
                            (match uu____9967 with
                             | (t_base,uu____9978) ->
                                 solve_t env
                                   (let uu___160_9993 = problem  in
                                    {
                                      FStar_TypeChecker_Common.pid =
                                        (uu___160_9993.FStar_TypeChecker_Common.pid);
                                      FStar_TypeChecker_Common.lhs = t_base;
                                      FStar_TypeChecker_Common.relation =
                                        FStar_TypeChecker_Common.EQ;
                                      FStar_TypeChecker_Common.rhs =
                                        (uu___160_9993.FStar_TypeChecker_Common.rhs);
                                      FStar_TypeChecker_Common.element =
                                        (uu___160_9993.FStar_TypeChecker_Common.element);
                                      FStar_TypeChecker_Common.logical_guard
                                        =
                                        (uu___160_9993.FStar_TypeChecker_Common.logical_guard);
                                      FStar_TypeChecker_Common.scope =
                                        (uu___160_9993.FStar_TypeChecker_Common.scope);
                                      FStar_TypeChecker_Common.reason =
                                        (uu___160_9993.FStar_TypeChecker_Common.reason);
                                      FStar_TypeChecker_Common.loc =
                                        (uu___160_9993.FStar_TypeChecker_Common.loc);
                                      FStar_TypeChecker_Common.rank =
                                        (uu___160_9993.FStar_TypeChecker_Common.rank)
                                    }) wl))
                   | (FStar_Syntax_Syntax.Tm_refine uu____9996,uu____9997) ->
                       let t2 =
                         let _0_616 = base_and_refinement env wl t2  in
                         FStar_All.pipe_left force_refinement _0_616  in
                       solve_t env
                         (let uu___161_10012 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___161_10012.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs =
                              (uu___161_10012.FStar_TypeChecker_Common.lhs);
                            FStar_TypeChecker_Common.relation =
                              (uu___161_10012.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t2;
                            FStar_TypeChecker_Common.element =
                              (uu___161_10012.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___161_10012.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___161_10012.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___161_10012.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___161_10012.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___161_10012.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (uu____10013,FStar_Syntax_Syntax.Tm_refine uu____10014)
                       ->
                       let t1 =
                         let _0_617 = base_and_refinement env wl t1  in
                         FStar_All.pipe_left force_refinement _0_617  in
                       solve_t env
                         (let uu___162_10029 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___162_10029.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t1;
                            FStar_TypeChecker_Common.relation =
                              (uu___162_10029.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs =
                              (uu___162_10029.FStar_TypeChecker_Common.rhs);
                            FStar_TypeChecker_Common.element =
                              (uu___162_10029.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___162_10029.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___162_10029.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___162_10029.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___162_10029.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___162_10029.FStar_TypeChecker_Common.rank)
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
                         let _0_618 = FStar_Syntax_Util.head_and_args t1  in
                         FStar_All.pipe_right _0_618 Prims.fst  in
                       let head2 =
                         let _0_619 = FStar_Syntax_Util.head_and_args t2  in
                         FStar_All.pipe_right _0_619 Prims.fst  in
                       let uu____10098 =
                         (((FStar_TypeChecker_Env.is_interpreted env head1)
                             ||
                             (FStar_TypeChecker_Env.is_interpreted env head2))
                            && wl.smt_ok)
                           &&
                           (problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.EQ)
                          in
                       (match uu____10098 with
                        | true  ->
                            let uv1 = FStar_Syntax_Free.uvars t1  in
                            let uv2 = FStar_Syntax_Free.uvars t2  in
                            let uu____10107 =
                              (FStar_Util.set_is_empty uv1) &&
                                (FStar_Util.set_is_empty uv2)
                               in
                            (match uu____10107 with
                             | true  ->
                                 let guard =
                                   let uu____10116 =
                                     let _0_620 =
                                       FStar_Syntax_Util.eq_tm t1 t2  in
                                     _0_620 = FStar_Syntax_Util.Equal  in
                                   match uu____10116 with
                                   | true  -> None
                                   | uu____10122 ->
                                       let _0_622 =
                                         FStar_Syntax_Util.mk_eq
                                           FStar_Syntax_Syntax.tun
                                           FStar_Syntax_Syntax.tun t1 t2
                                          in
                                       FStar_All.pipe_left
                                         (fun _0_621  -> Some _0_621) _0_622
                                    in
                                 let _0_623 = solve_prob orig guard [] wl  in
                                 solve env _0_623
                             | uu____10130 ->
                                 rigid_rigid_delta env orig wl head1 head2 t1
                                   t2)
                        | uu____10131 ->
                            rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   | (FStar_Syntax_Syntax.Tm_ascribed
                      (t1,uu____10133,uu____10134),uu____10135) ->
                       solve_t' env
                         (let uu___163_10154 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___163_10154.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t1;
                            FStar_TypeChecker_Common.relation =
                              (uu___163_10154.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs =
                              (uu___163_10154.FStar_TypeChecker_Common.rhs);
                            FStar_TypeChecker_Common.element =
                              (uu___163_10154.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___163_10154.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___163_10154.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___163_10154.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___163_10154.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___163_10154.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (uu____10157,FStar_Syntax_Syntax.Tm_ascribed
                      (t2,uu____10159,uu____10160)) ->
                       solve_t' env
                         (let uu___164_10179 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___164_10179.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs =
                              (uu___164_10179.FStar_TypeChecker_Common.lhs);
                            FStar_TypeChecker_Common.relation =
                              (uu___164_10179.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t2;
                            FStar_TypeChecker_Common.element =
                              (uu___164_10179.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___164_10179.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.scope =
                              (uu___164_10179.FStar_TypeChecker_Common.scope);
                            FStar_TypeChecker_Common.reason =
                              (uu___164_10179.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___164_10179.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___164_10179.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Syntax_Syntax.Tm_let _,_)
                     |(FStar_Syntax_Syntax.Tm_meta _,_)
                      |(FStar_Syntax_Syntax.Tm_delayed _,_)
                       |(_,FStar_Syntax_Syntax.Tm_meta _)
                        |(_,FStar_Syntax_Syntax.Tm_delayed _)
                         |(_,FStar_Syntax_Syntax.Tm_let _)
                       ->
                       failwith
                         (let _0_625 = FStar_Syntax_Print.tag_of_term t1  in
                          let _0_624 = FStar_Syntax_Print.tag_of_term t2  in
                          FStar_Util.format2 "Impossible: %s and %s" _0_625
                            _0_624)
                   | uu____10192 -> giveup env "head tag mismatch" orig)))

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
          (let uu____11442 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           match uu____10224 with
           | true  ->
               FStar_Util.print_string
                 "solve_c is using an equality constraint\n"
           | uu____10225 -> ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____11450  ->
                  fun uu____11451  ->
                    match (uu____11450, uu____11451) with
                    | ((a1,uu____11461),(a2,uu____11463)) ->
                        let uu____11468 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_68  -> FStar_TypeChecker_Common.TProb _0_68)
                          uu____11468)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             FStar_Syntax_Util.mk_conj_l
               (FStar_List.map
                  (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                  sub_probs)
              in
           let wl = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl))
           in
        let solve_sub c1 edge c2 =
          let r = FStar_TypeChecker_Env.get_range env  in
          match problem.FStar_TypeChecker_Common.relation =
                  FStar_TypeChecker_Common.EQ
          with
          | true  ->
              let wp =
                match c1.FStar_Syntax_Syntax.effect_args with
                | (wp1,uu____10274)::[] -> wp1
                | uu____10287 ->
                    failwith
                      (let _0_628 =
                         FStar_Range.string_of_range
                           (FStar_Ident.range_of_lid
                              c1.FStar_Syntax_Syntax.effect_name)
                          in
                       FStar_Util.format1
                         "Unexpected number of indices on a normalized effect (%s)"
                         _0_628)
                 in
              let c1 =
                let _0_630 =
                  let _0_629 =
                    FStar_Syntax_Syntax.as_arg
                      (edge.FStar_TypeChecker_Env.mlift
                         c1.FStar_Syntax_Syntax.result_typ wp)
                     in
                  [_0_629]  in
                {
                  FStar_Syntax_Syntax.comp_univs =
                    (c1.FStar_Syntax_Syntax.comp_univs);
                  FStar_Syntax_Syntax.effect_name =
                    (c2.FStar_Syntax_Syntax.effect_name);
                  FStar_Syntax_Syntax.result_typ =
                    (c1.FStar_Syntax_Syntax.result_typ);
                  FStar_Syntax_Syntax.effect_args = _0_630;
                  FStar_Syntax_Syntax.flags = (c1.FStar_Syntax_Syntax.flags)
                }  in
              solve_eq c1 c2
          | uu____10296 ->
              let is_null_wp_2 =
                FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___126_10299  ->
                        match uu___126_10299 with
                        | FStar_Syntax_Syntax.TOTAL 
                          |FStar_Syntax_Syntax.MLEFFECT 
                           |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                        | uu____10300 -> false))
                 in
              let uu____10301 =
                match ((c1.FStar_Syntax_Syntax.effect_args),
                        (c2.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1,uu____10325)::uu____10326,(wp2,uu____10328)::uu____10329)
                    -> (wp1, wp2)
                | uu____10370 ->
                    failwith
                      (let _0_632 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_Syntax_Syntax.effect_name
                          in
                       let _0_631 =
                         FStar_Syntax_Print.lid_to_string
                           c2.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Got effects %s and %s, expected normalized effects"
                         _0_632 _0_631)
                 in
              (match uu____10301 with
               | (wpc1,wpc2) ->
                   let uu____10399 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   (match uu____10399 with
                    | true  ->
                        let _0_633 =
                          problem_using_guard orig
                            c1.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c2.FStar_Syntax_Syntax.result_typ None
                            "result type"
                           in
                        solve_t env _0_633 wl
                    | uu____10404 ->
                        let c2_decl =
                          FStar_TypeChecker_Env.get_effect_decl env
                            c2.FStar_Syntax_Syntax.effect_name
                           in
                        let g =
                          match env.FStar_TypeChecker_Env.lax with
                          | true  -> FStar_Syntax_Util.t_true
                          | uu____10407 ->
                              (match is_null_wp_2 with
                               | true  ->
                                   ((let uu____10409 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     match uu____10409 with
                                     | true  ->
                                         FStar_Util.print_string
                                           "Using trivial wp ... \n"
                                     | uu____10410 -> ());
                                    (FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_app
                                          (let _0_641 =
                                             let _0_635 =
                                               let _0_634 =
                                                 env.FStar_TypeChecker_Env.universe_of
                                                   env
                                                   c1.FStar_Syntax_Syntax.result_typ
                                                  in
                                               [_0_634]  in
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               _0_635 env c2_decl
                                               c2_decl.FStar_Syntax_Syntax.trivial
                                              in
                                           let _0_640 =
                                             let _0_639 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1.FStar_Syntax_Syntax.result_typ
                                                in
                                             let _0_638 =
                                               let _0_637 =
                                                 let _0_636 =
                                                   edge.FStar_TypeChecker_Env.mlift
                                                     c1.FStar_Syntax_Syntax.result_typ
                                                     wpc1
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   _0_636
                                                  in
                                               [_0_637]  in
                                             _0_639 :: _0_638  in
                                           (_0_641, _0_640))))
                                      (Some
                                         (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                      r)
                               | uu____10420 ->
                                   (FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (let _0_651 =
                                            let _0_643 =
                                              let _0_642 =
                                                env.FStar_TypeChecker_Env.universe_of
                                                  env
                                                  c2.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [_0_642]  in
                                            FStar_TypeChecker_Env.inst_effect_fun_with
                                              _0_643 env c2_decl
                                              c2_decl.FStar_Syntax_Syntax.stronger
                                             in
                                          let _0_650 =
                                            let _0_649 =
                                              FStar_Syntax_Syntax.as_arg
                                                c2.FStar_Syntax_Syntax.result_typ
                                               in
                                            let _0_648 =
                                              let _0_647 =
                                                FStar_Syntax_Syntax.as_arg
                                                  wpc2
                                                 in
                                              let _0_646 =
                                                let _0_645 =
                                                  let _0_644 =
                                                    edge.FStar_TypeChecker_Env.mlift
                                                      c1.FStar_Syntax_Syntax.result_typ
                                                      wpc1
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_Syntax_Syntax.as_arg
                                                    _0_644
                                                   in
                                                [_0_645]  in
                                              _0_647 :: _0_646  in
                                            _0_649 :: _0_648  in
                                          (_0_651, _0_650))))
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r)
                           in
                        let base_prob =
                          let _0_653 =
                            sub_prob c1.FStar_Syntax_Syntax.result_typ
                              problem.FStar_TypeChecker_Common.relation
                              c2.FStar_Syntax_Syntax.result_typ "result type"
                             in
                          FStar_All.pipe_left
                            (fun _0_652  ->
                               FStar_TypeChecker_Common.TProb _0_652) _0_653
                           in
                        let wl =
                          let _0_657 =
                            let _0_656 =
                              let _0_655 =
                                FStar_All.pipe_right (p_guard base_prob)
                                  Prims.fst
                                 in
                              FStar_Syntax_Util.mk_conj _0_655 g  in
                            FStar_All.pipe_left (fun _0_654  -> Some _0_654)
                              _0_656
                             in
                          solve_prob orig _0_657 [] wl  in
                        solve env (attempt [base_prob] wl)))
           in
        let uu____10443 = FStar_Util.physical_equality c1 c2  in
        match uu____10443 with
        | true  ->
            let _0_658 = solve_prob orig None [] wl  in solve env _0_658
        | uu____10444 ->
            ((let uu____10446 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              match uu____10446 with
              | true  ->
                  let _0_660 = FStar_Syntax_Print.comp_to_string c1  in
                  let _0_659 = FStar_Syntax_Print.comp_to_string c2  in
                  FStar_Util.print3 "solve_c %s %s %s\n" _0_660
                    (rel_to_string problem.FStar_TypeChecker_Common.relation)
                    _0_659
              | uu____10447 -> ());
             (let uu____10448 =
                let _0_662 = FStar_TypeChecker_Normalize.ghost_to_pure env c1
                   in
                let _0_661 = FStar_TypeChecker_Normalize.ghost_to_pure env c2
                   in
                (_0_662, _0_661)  in
              match uu____10448 with
              | (c1,c2) ->
                  (match ((c1.FStar_Syntax_Syntax.n),
                           (c2.FStar_Syntax_Syntax.n))
                   with
                   | (FStar_Syntax_Syntax.GTotal
                      (t1,uu____10454),FStar_Syntax_Syntax.Total
                      (t2,uu____10456)) when
                       FStar_Syntax_Util.non_informative t2 ->
                       let _0_663 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2 None
                           "result type"
                          in
                       solve_t env _0_663 wl
                   | (FStar_Syntax_Syntax.GTotal
                      uu____10471,FStar_Syntax_Syntax.Total uu____10472) ->
                       giveup env "incompatible monad ordering: GTot </: Tot"
                         orig
                   | (FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                     |(FStar_Syntax_Syntax.GTotal
                       (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                      |(FStar_Syntax_Syntax.Total
                        (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                       ->
                       let _0_664 =
                         problem_using_guard orig t1
                           problem.FStar_TypeChecker_Common.relation t2 None
                           "result type"
                          in
                       solve_t env _0_664 wl
                   | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp
                      _)
                     |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp
                       _) ->
                       let _0_667 =
                         let uu___165_10527 = problem  in
                         let _0_666 =
                           let _0_665 =
                             FStar_TypeChecker_Normalize.comp_to_comp_typ env
                               c1
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                             _0_665
                            in
                         {
                           FStar_TypeChecker_Common.pid =
                             (uu___165_10527.FStar_TypeChecker_Common.pid);
                           FStar_TypeChecker_Common.lhs = _0_666;
                           FStar_TypeChecker_Common.relation =
                             (uu___165_10527.FStar_TypeChecker_Common.relation);
                           FStar_TypeChecker_Common.rhs =
                             (uu___165_10527.FStar_TypeChecker_Common.rhs);
                           FStar_TypeChecker_Common.element =
                             (uu___165_10527.FStar_TypeChecker_Common.element);
                           FStar_TypeChecker_Common.logical_guard =
                             (uu___165_10527.FStar_TypeChecker_Common.logical_guard);
                           FStar_TypeChecker_Common.scope =
                             (uu___165_10527.FStar_TypeChecker_Common.scope);
                           FStar_TypeChecker_Common.reason =
                             (uu___165_10527.FStar_TypeChecker_Common.reason);
                           FStar_TypeChecker_Common.loc =
                             (uu___165_10527.FStar_TypeChecker_Common.loc);
                           FStar_TypeChecker_Common.rank =
                             (uu___165_10527.FStar_TypeChecker_Common.rank)
                         }  in
                       solve_c env _0_667 wl
                   | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal
                      _)
                     |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total
                       _) ->
                       let _0_670 =
                         let uu___166_10534 = problem  in
                         let _0_669 =
                           let _0_668 =
                             FStar_TypeChecker_Normalize.comp_to_comp_typ env
                               c2
                              in
                           FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                             _0_668
                            in
                         {
                           FStar_TypeChecker_Common.pid =
                             (uu___166_10534.FStar_TypeChecker_Common.pid);
                           FStar_TypeChecker_Common.lhs =
                             (uu___166_10534.FStar_TypeChecker_Common.lhs);
                           FStar_TypeChecker_Common.relation =
                             (uu___166_10534.FStar_TypeChecker_Common.relation);
                           FStar_TypeChecker_Common.rhs = _0_669;
                           FStar_TypeChecker_Common.element =
                             (uu___166_10534.FStar_TypeChecker_Common.element);
                           FStar_TypeChecker_Common.logical_guard =
                             (uu___166_10534.FStar_TypeChecker_Common.logical_guard);
                           FStar_TypeChecker_Common.scope =
                             (uu___166_10534.FStar_TypeChecker_Common.scope);
                           FStar_TypeChecker_Common.reason =
                             (uu___166_10534.FStar_TypeChecker_Common.reason);
                           FStar_TypeChecker_Common.loc =
                             (uu___166_10534.FStar_TypeChecker_Common.loc);
                           FStar_TypeChecker_Common.rank =
                             (uu___166_10534.FStar_TypeChecker_Common.rank)
                         }  in
                       solve_c env _0_670 wl
                   | (FStar_Syntax_Syntax.Comp
                      uu____10537,FStar_Syntax_Syntax.Comp uu____10538) ->
                       let uu____10539 =
                         ((FStar_Syntax_Util.is_ml_comp c1) &&
                            (FStar_Syntax_Util.is_ml_comp c2))
                           ||
                           ((FStar_Syntax_Util.is_total_comp c1) &&
                              ((FStar_Syntax_Util.is_total_comp c2) ||
                                 (FStar_Syntax_Util.is_ml_comp c2)))
                          in
                       (match uu____10539 with
                        | true  ->
                            let _0_671 =
                              problem_using_guard orig
                                (FStar_Syntax_Util.comp_result c1)
                                problem.FStar_TypeChecker_Common.relation
                                (FStar_Syntax_Util.comp_result c2) None
                                "result type"
                               in
                            solve_t env _0_671 wl
                        | uu____10542 ->
                            let c1_comp =
                              FStar_TypeChecker_Normalize.comp_to_comp_typ
                                env c1
                               in
                            let c2_comp =
                              FStar_TypeChecker_Normalize.comp_to_comp_typ
                                env c2
                               in
                            (match (problem.FStar_TypeChecker_Common.relation
                                      = FStar_TypeChecker_Common.EQ)
                                     &&
                                     (FStar_Ident.lid_equals
                                        c1_comp.FStar_Syntax_Syntax.effect_name
                                        c2_comp.FStar_Syntax_Syntax.effect_name)
                             with
                             | true  -> solve_eq c1_comp c2_comp
                             | uu____10545 ->
                                 let c1 =
                                   FStar_TypeChecker_Normalize.unfold_effect_abbrev
                                     env c1
                                    in
                                 let c2 =
                                   FStar_TypeChecker_Normalize.unfold_effect_abbrev
                                     env c2
                                    in
                                 ((let uu____10549 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   match uu____10549 with
                                   | true  ->
                                       FStar_Util.print2
                                         "solve_c for %s and %s\n"
                                         (c1.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                         (c2.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                   | uu____10550 -> ());
                                  (let uu____10551 =
                                     FStar_TypeChecker_Env.monad_leq env
                                       c1.FStar_Syntax_Syntax.effect_name
                                       c2.FStar_Syntax_Syntax.effect_name
                                      in
                                   match uu____10551 with
                                   | None  ->
                                       let uu____10553 =
                                         ((FStar_Syntax_Util.is_ghost_effect
                                             c1.FStar_Syntax_Syntax.effect_name)
                                            &&
                                            (FStar_Syntax_Util.is_pure_effect
                                               c2.FStar_Syntax_Syntax.effect_name))
                                           &&
                                           (FStar_Syntax_Util.non_informative
                                              (FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Normalize.Eager_unfolding;
                                                 FStar_TypeChecker_Normalize.UnfoldUntil
                                                   FStar_Syntax_Syntax.Delta_constant]
                                                 env
                                                 c2.FStar_Syntax_Syntax.result_typ))
                                          in
                                       (match uu____10553 with
                                        | true  ->
                                            let edge =
                                              {
                                                FStar_TypeChecker_Env.msource
                                                  =
                                                  (c1.FStar_Syntax_Syntax.effect_name);
                                                FStar_TypeChecker_Env.mtarget
                                                  =
                                                  (c2.FStar_Syntax_Syntax.effect_name);
                                                FStar_TypeChecker_Env.mlift =
                                                  (fun r  -> fun t  -> t)
                                              }  in
                                            solve_sub c1 edge c2
                                        | uu____10557 ->
                                            let _0_674 =
                                              let _0_673 =
                                                FStar_Syntax_Print.lid_to_string
                                                  c1.FStar_Syntax_Syntax.effect_name
                                                 in
                                              let _0_672 =
                                                FStar_Syntax_Print.lid_to_string
                                                  c2.FStar_Syntax_Syntax.effect_name
                                                 in
                                              FStar_Util.format2
                                                "incompatible monad ordering: %s </: %s"
                                                _0_673 _0_672
                                               in
                                            giveup env _0_674 orig)
                                   | Some edge -> solve_sub c1 edge c2)))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____11912 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____10581  ->
              match uu____10581 with
              | (uu____10592,uu____10593,u,uu____10595,uu____10596,uu____10597)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right _0_675 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____11977 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right _0_676 (FStar_String.concat ", ")  in
    let ineqs =
      let _0_679 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____11999  ->
                match uu____11999 with
                | (u1,u2) ->
                    let _0_678 = FStar_Syntax_Print.univ_to_string u1  in
                    let _0_677 = FStar_Syntax_Print.univ_to_string u2  in
                    FStar_Util.format2 "%s < %s" _0_678 _0_677))
         in
      FStar_All.pipe_right _0_679 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs
  
let guard_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____12017,[])) -> "{}"
      | uu____12030 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____12040 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                (match uu____10682 with
                 | true  -> FStar_TypeChecker_Normalize.term_to_string env f
                 | uu____10683 -> "non-trivial")
             in
          let carry =
            let uu____12043 =
              FStar_List.map
                (fun uu____10688  ->
                   match uu____10688 with
                   | (uu____10691,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right _0_680 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let _0_681 = ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry _0_681 imps
  
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
        FStar_TypeChecker_Env.univ_ineqs = uu____10713;
        FStar_TypeChecker_Env.implicits = uu____10714;_} -> true
    | uu____10728 -> false
  
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
      | Some g ->
          let f =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____10755 -> failwith "impossible"  in
          Some
            (let uu___167_10756 = g  in
             let _0_690 =
               let _0_689 =
                 let _0_688 =
                   let _0_683 = FStar_Syntax_Syntax.mk_binder x  in [_0_683]
                    in
                 let _0_687 =
                   Some
                     (let _0_686 =
                        let _0_684 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right _0_684
                          FStar_Syntax_Util.lcomp_of_comp
                         in
                      FStar_All.pipe_right _0_686
                        (fun _0_685  -> FStar_Util.Inl _0_685))
                    in
                 FStar_Syntax_Util.abs _0_688 f _0_687  in
               FStar_All.pipe_left
                 (fun _0_682  -> FStar_TypeChecker_Common.NonTrivial _0_682)
                 _0_689
                in
             {
               FStar_TypeChecker_Env.guard_f = _0_690;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_10756.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_10756.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_10756.FStar_TypeChecker_Env.implicits)
             })
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___168_10777 = g  in
          let _0_695 =
            let _0_694 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (let _0_693 =
                       let _0_692 = FStar_Syntax_Syntax.as_arg e  in [_0_692]
                        in
                     (f, _0_693))))
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_691  -> FStar_TypeChecker_Common.NonTrivial _0_691)
              _0_694
             in
          {
            FStar_TypeChecker_Env.guard_f = _0_695;
            FStar_TypeChecker_Env.deferred =
              (uu___168_10777.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___168_10777.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___168_10777.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____10794 ->
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
          FStar_TypeChecker_Common.NonTrivial
            (FStar_Syntax_Util.mk_conj f1 f2)
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____10812 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let _0_696 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = _0_696;
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
          let uu___169_10880 = g  in
          let _0_699 =
            let _0_698 = FStar_Syntax_Util.close_forall binders f  in
            FStar_All.pipe_right _0_698
              (fun _0_697  -> FStar_TypeChecker_Common.NonTrivial _0_697)
             in
          {
            FStar_TypeChecker_Env.guard_f = _0_699;
            FStar_TypeChecker_Env.deferred =
              (uu___169_10880.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___169_10880.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___169_10880.FStar_TypeChecker_Env.implicits)
          }
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____12092 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    match uu____10918 with
    | true  ->
        let _0_701 = FStar_TypeChecker_Normalize.term_to_string env lhs  in
        let _0_700 = FStar_TypeChecker_Normalize.term_to_string env rhs  in
        FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _0_701
          (rel_to_string rel) _0_700
    | uu____10919 -> "TOP"  in
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
            let _0_704 =
              let _0_703 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_702  -> Some _0_702) _0_703  in
            FStar_Syntax_Syntax.new_bv _0_704 t1  in
          let env = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let _0_708 =
              let _0_706 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_705  -> Some _0_705) _0_706  in
            let _0_707 = FStar_TypeChecker_Env.get_range env  in
            new_t_problem env t1 rel t2 _0_708 _0_707  in
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
        let probs =
          let uu____10966 = FStar_Options.eager_inference ()  in
          match uu____10966 with
          | true  ->
              let uu___170_10967 = probs  in
              {
                attempting = (uu___170_10967.attempting);
                wl_deferred = (uu___170_10967.wl_deferred);
                ctr = (uu___170_10967.ctr);
                defer_ok = false;
                smt_ok = (uu___170_10967.smt_ok);
                tcenv = (uu___170_10967.tcenv)
              }
          | uu____10968 -> probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs  in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____12161 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              match uu____10978 with
              | true  ->
                  let _0_709 = explain env d s  in
                  FStar_All.pipe_left FStar_Util.print_string _0_709
              | uu____10979 -> ());
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
          ((let uu____12172 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            match uu____10988 with
            | true  ->
                let _0_710 = FStar_Syntax_Print.term_to_string f  in
                FStar_Util.print1 "Simplifying guard %s\n" _0_710
            | uu____10989 -> ());
           (let f =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____10992 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             match uu____10992 with
             | true  ->
                 let _0_711 = FStar_Syntax_Print.term_to_string f  in
                 FStar_Util.print1 "Simplified guard to %s\n" _0_711
             | uu____10993 -> ());
            (let f =
               let uu____10995 =
                 (FStar_Syntax_Util.unmeta f).FStar_Syntax_Syntax.n  in
               match uu____10995 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____10997 -> FStar_TypeChecker_Common.NonTrivial f  in
             let uu___171_10998 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___176_12187.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___176_12187.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___176_12187.FStar_TypeChecker_Env.implicits)
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
            let _0_717 =
              let _0_716 =
                let _0_715 =
                  let _0_714 = FStar_All.pipe_right (p_guard prob) Prims.fst
                     in
                  FStar_All.pipe_right _0_714
                    (fun _0_713  ->
                       FStar_TypeChecker_Common.NonTrivial _0_713)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____12204;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env _0_716  in
            FStar_All.pipe_left (fun _0_712  -> Some _0_712) _0_717
  
let try_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____11036 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         match uu____11036 with
         | true  ->
             let _0_719 = FStar_Syntax_Print.term_to_string t1  in
             let _0_718 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" _0_719 _0_718
         | uu____11037 -> ());
        (let prob =
           let _0_722 =
             let _0_721 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _0_721
              in
           FStar_All.pipe_left
             (fun _0_720  -> FStar_TypeChecker_Common.TProb _0_720) _0_722
            in
         let g =
           let _0_724 =
             let _0_723 = singleton env prob  in
             solve_and_commit env _0_723 (fun uu____11045  -> None)  in
           FStar_All.pipe_left (with_guard env prob) _0_724  in
         g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____11057 = try_teq env t1 t2  in
        match uu____11057 with
        | None  ->
            Prims.raise
              (FStar_Errors.Error
                 (let _0_726 =
                    FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                  let _0_725 = FStar_TypeChecker_Env.get_range env  in
                  (_0_726, _0_725)))
        | Some g ->
            ((let uu____12272 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              match uu____11061 with
              | true  ->
                  let _0_729 = FStar_Syntax_Print.term_to_string t1  in
                  let _0_728 = FStar_Syntax_Print.term_to_string t2  in
                  let _0_727 = guard_to_string env g  in
                  FStar_Util.print3
                    "teq of %s and %s succeeded with guard %s\n" _0_729
                    _0_728 _0_727
              | uu____11062 -> ());
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
          (let uu____12291 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           match uu____11077 with
           | true  ->
               let _0_731 = FStar_TypeChecker_Normalize.term_to_string env t1
                  in
               let _0_730 = FStar_TypeChecker_Normalize.term_to_string env t2
                  in
               FStar_Util.print2 "try_subtype of %s and %s\n" _0_731 _0_730
           | uu____11078 -> ());
          (let uu____11079 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____11079 with
           | (prob,x) ->
               let g =
                 let _0_733 =
                   let _0_732 = singleton' env prob smt_ok  in
                   solve_and_commit env _0_732 (fun uu____11089  -> None)  in
                 FStar_All.pipe_left (with_guard env prob) _0_733  in
               ((let uu____11093 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 match uu____11093 with
                 | true  ->
                     let _0_737 =
                       FStar_TypeChecker_Normalize.term_to_string env t1  in
                     let _0_736 =
                       FStar_TypeChecker_Normalize.term_to_string env t2  in
                     let _0_735 =
                       let _0_734 = FStar_Util.must g  in
                       guard_to_string env _0_734  in
                     FStar_Util.print3
                       "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                       _0_737 _0_736 _0_735
                 | uu____11094 -> ());
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
          let _0_739 = FStar_TypeChecker_Env.get_range env  in
          let _0_738 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.report _0_739 _0_738
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____12353 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         match uu____11128 with
         | true  ->
             let _0_741 = FStar_Syntax_Print.comp_to_string c1  in
             let _0_740 = FStar_Syntax_Print.comp_to_string c2  in
             FStar_Util.print2 "sub_comp of %s and %s\n" _0_741 _0_740
         | uu____11129 -> ());
        (let rel =
           match env.FStar_TypeChecker_Env.use_eq with
           | true  -> FStar_TypeChecker_Common.EQ
           | uu____11131 -> FStar_TypeChecker_Common.SUB  in
         let prob =
           let _0_744 =
             let _0_743 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None _0_743 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_742  -> FStar_TypeChecker_Common.CProb _0_742) _0_744
            in
         let _0_746 =
           let _0_745 = singleton env prob  in
           solve_and_commit env _0_745 (fun uu____11137  -> None)  in
         FStar_All.pipe_left (with_guard env prob) _0_746)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____12388  ->
        match uu____12388 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              Prims.raise
                (FStar_Errors.Error
                   (let _0_750 =
                      let _0_748 = FStar_Syntax_Print.univ_to_string u1  in
                      let _0_747 = FStar_Syntax_Print.univ_to_string u2  in
                      FStar_Util.format2
                        "Universe %s and %s are incompatible" _0_748 _0_747
                       in
                    let _0_749 = FStar_TypeChecker_Env.get_range env  in
                    (_0_750, _0_749)))
               in
            let equiv v v' =
              let uu____11186 =
                let _0_752 = FStar_Syntax_Subst.compress_univ v  in
                let _0_751 = FStar_Syntax_Subst.compress_univ v'  in
                (_0_752, _0_751)  in
              match uu____11186 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____11196 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____11210 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____11210 with
                      | FStar_Syntax_Syntax.U_unif uu____11214 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____12469  ->
                                    match uu____12469 with
                                    | (u,v') ->
                                        let uu____11231 = equiv v v'  in
                                        (match uu____11231 with
                                         | true  ->
                                             let uu____11233 =
                                               FStar_All.pipe_right variables
                                                 (FStar_Util.for_some
                                                    (equiv u))
                                                in
                                             (match uu____11233 with
                                              | true  -> []
                                              | uu____11236 -> [u])
                                         | uu____11237 -> [])))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____11243 -> []))
               in
            let uu____11246 =
              let wl =
                let uu___172_11249 = empty_worklist env  in
                {
                  attempting = (uu___177_12493.attempting);
                  wl_deferred = (uu___177_12493.wl_deferred);
                  ctr = (uu___177_12493.ctr);
                  defer_ok = false;
                  smt_ok = (uu___172_11249.smt_ok);
                  tcenv = (uu___172_11249.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____11256  ->
                      match uu____11256 with
                      | (lb,v) ->
                          let uu____11261 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v
                             in
                          (match uu____11261 with
                           | USolved wl -> ()
                           | uu____11263 -> fail lb v)))
               in
            let rec check_ineq uu____11269 =
              match uu____11269 with
              | (u,v) ->
                  let u =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u, v) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____11276) -> true
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
                   | (FStar_Syntax_Syntax.U_max us,uu____12536) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____12540,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v  -> check_ineq (u, v)))
                   | uu____11301 -> false)
               in
            let uu____11304 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____11310  ->
                      match uu____11310 with
                      | (u,v) ->
                          let uu____11315 = check_ineq (u, v)  in
                          (match uu____11315 with
                           | true  -> true
                           | uu____11316 ->
                               ((let uu____11318 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "GenUniverses")
                                    in
                                 match uu____11318 with
                                 | true  ->
                                     let _0_754 =
                                       FStar_Syntax_Print.univ_to_string u
                                        in
                                     let _0_753 =
                                       FStar_Syntax_Print.univ_to_string v
                                        in
                                     FStar_Util.print2 "%s </= %s" _0_754
                                       _0_753
                                 | uu____11319 -> ());
                                false))))
               in
            (match uu____11304 with
             | true  -> ()
             | uu____11320 ->
                 ((let uu____11322 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "GenUniverses")
                      in
                   match uu____11322 with
                   | true  ->
                       ((let _0_755 = ineqs_to_string (variables, ineqs)  in
                         FStar_Util.print1
                           "Partially solved inequality constraints are: %s\n"
                           _0_755);
                        FStar_Unionfind.rollback tx;
                        (let _0_756 = ineqs_to_string (variables, ineqs)  in
                         FStar_Util.print1
                           "Original solved inequality constraints are: %s\n"
                           _0_756))
                   | uu____11333 -> ());
                  Prims.raise
                    (FStar_Errors.Error
                       (let _0_757 = FStar_TypeChecker_Env.get_range env  in
                        ("Failed to solve universe inequalities for inductives",
                          _0_757)))))
  
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
      let fail uu____12619 =
        match uu____12619 with
        | (d,s) ->
            let msg = explain env d s  in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____11376 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       match uu____11376 with
       | true  ->
           let _0_759 = wl_to_string wl  in
           let _0_758 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Env.implicits)
              in
           FStar_Util.print2
             "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
             _0_759 _0_758
       | uu____11386 -> ());
      (let g =
         let uu____11388 = solve_and_commit env wl fail  in
         match uu____11388 with
         | Some [] ->
             let uu___173_11395 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___178_12650.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___178_12650.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___178_12650.FStar_TypeChecker_Env.implicits)
             }
         | uu____11398 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___174_11401 = g  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___179_12656.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___179_12656.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___179_12656.FStar_TypeChecker_Env.implicits)
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
          let g = solve_deferred_constraints env g  in
          let ret_g =
            let uu___175_11427 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___180_12682.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___180_12682.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___175_11427.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____11428 =
            Prims.op_Negation (FStar_TypeChecker_Env.should_verify env)  in
          match uu____11428 with
          | true  -> Some ret_g
          | uu____11430 ->
              (match g.FStar_TypeChecker_Env.guard_f with
               | FStar_TypeChecker_Common.Trivial  -> Some ret_g
               | FStar_TypeChecker_Common.NonTrivial vc ->
                   ((let uu____11434 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Norm")
                        in
                     match uu____11434 with
                     | true  ->
                         let _0_762 = FStar_TypeChecker_Env.get_range env  in
                         let _0_761 =
                           let _0_760 = FStar_Syntax_Print.term_to_string vc
                              in
                           FStar_Util.format1
                             "Before normalization VC=\n%s\n" _0_760
                            in
                         FStar_Errors.diag _0_762 _0_761
                     | uu____11435 -> ());
                    (let vc =
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                         FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.Simplify] env vc
                        in
                     match check_trivial vc with
                     | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc ->
                         (match Prims.op_Negation use_smt with
                          | true  -> None
                          | uu____11440 ->
                              ((let uu____11443 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                match uu____11443 with
                                | true  ->
                                    let _0_765 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    let _0_764 =
                                      let _0_763 =
                                        FStar_Syntax_Print.term_to_string vc
                                         in
                                      FStar_Util.format1 "Checking VC=\n%s\n"
                                        _0_763
                                       in
                                    FStar_Errors.diag _0_765 _0_764
                                | uu____11444 -> ());
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                 use_env_range_msg env vc;
                               Some ret_g)))))
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____11451 = discharge_guard' None env g true  in
      match uu____11451 with
      | Some g -> g
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____11471 = FStar_Unionfind.find u  in
      match uu____11471 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____11480 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____11495 = acc  in
      match uu____11495 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               (match Prims.op_Negation changed with
                | true  -> out
                | uu____11506 -> until_fixpoint ([], false) out)
           | hd::tl ->
               let uu____11541 = hd  in
               (match uu____11541 with
                | (uu____11548,env,u,tm,k,r) ->
                    let uu____11554 = unresolved u  in
                    (match uu____11554 with
                     | true  -> until_fixpoint ((hd :: out), changed) tl
                     | uu____11568 ->
                         let env =
                           FStar_TypeChecker_Env.set_expected_typ env k  in
                         let tm =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env tm
                            in
                         ((let uu____11572 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "RelCheck")
                              in
                           match uu____11572 with
                           | true  ->
                               let _0_768 =
                                 FStar_Syntax_Print.uvar_to_string u  in
                               let _0_767 =
                                 FStar_Syntax_Print.term_to_string tm  in
                               let _0_766 =
                                 FStar_Syntax_Print.term_to_string k  in
                               FStar_Util.print3
                                 "Checking uvar %s resolved to %s at type %s\n"
                                 _0_768 _0_767 _0_766
                           | uu____11576 -> ());
                          (let uu____11577 =
                             env.FStar_TypeChecker_Env.type_of
                               (let uu___176_11581 = env  in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___176_11581.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___176_11581.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___176_11581.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (uu___176_11581.FStar_TypeChecker_Env.gamma);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___176_11581.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___176_11581.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___176_11581.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___176_11581.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.is_pattern =
                                    (uu___176_11581.FStar_TypeChecker_Env.is_pattern);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___176_11581.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___176_11581.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___176_11581.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___176_11581.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___176_11581.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___176_11581.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq =
                                    (uu___176_11581.FStar_TypeChecker_Env.use_eq);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___176_11581.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___176_11581.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___176_11581.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___176_11581.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.type_of =
                                    (uu___176_11581.FStar_TypeChecker_Env.type_of);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___176_11581.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.use_bv_sorts = true;
                                  FStar_TypeChecker_Env.qname_and_index =
                                    (uu___176_11581.FStar_TypeChecker_Env.qname_and_index)
                                }) tm
                              in
                           match uu____11577 with
                           | (uu____11582,uu____11583,g) ->
                               let g =
                                 match env.FStar_TypeChecker_Env.is_pattern
                                 with
                                 | true  ->
                                     let uu___177_11586 = g  in
                                     {
                                       FStar_TypeChecker_Env.guard_f =
                                         FStar_TypeChecker_Common.Trivial;
                                       FStar_TypeChecker_Env.deferred =
                                         (uu___177_11586.FStar_TypeChecker_Env.deferred);
                                       FStar_TypeChecker_Env.univ_ineqs =
                                         (uu___177_11586.FStar_TypeChecker_Env.univ_ineqs);
                                       FStar_TypeChecker_Env.implicits =
                                         (uu___177_11586.FStar_TypeChecker_Env.implicits)
                                     }
                                 | uu____11587 -> g  in
                               let g' =
                                 let uu____11589 =
                                   discharge_guard'
                                     (Some
                                        (fun uu____11593  ->
                                           FStar_Syntax_Print.term_to_string
                                             tm)) env g true
                                    in
                                 match uu____11589 with
                                 | Some g -> g
                                 | None  ->
                                     failwith
                                       "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                  in
                               until_fixpoint
                                 ((FStar_List.append
                                     g'.FStar_TypeChecker_Env.implicits out),
                                   true) tl)))))
       in
    let uu___178_11608 = g  in
    let _0_769 = until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits
       in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___183_12896.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___183_12896.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___183_12896.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____12897
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g =
        let _0_770 = solve_deferred_constraints env g  in
        FStar_All.pipe_right _0_770 resolve_implicits  in
      match g.FStar_TypeChecker_Env.implicits with
      | [] ->
          let _0_771 = discharge_guard env g  in
          FStar_All.pipe_left Prims.ignore _0_771
      | (reason,uu____11636,uu____11637,e,t,r)::uu____11641 ->
          let _0_774 =
            let _0_773 = FStar_Syntax_Print.term_to_string t  in
            let _0_772 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              _0_773 _0_772 reason
             in
          FStar_Errors.report r _0_774
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___179_11661 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___184_12962.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___184_12962.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___184_12962.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____11679 = try_teq env t1 t2  in
        match uu____11679 with
        | None  -> false
        | Some g ->
            let uu____11682 = discharge_guard' None env g false  in
            (match uu____11682 with
             | Some uu____11686 -> true
             | None  -> false)
  