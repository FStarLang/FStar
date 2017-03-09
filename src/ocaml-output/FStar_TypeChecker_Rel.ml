open Prims
let new_uvar:
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.typ)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar in
        match binders with
        | [] ->
            let uv =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k)))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (uv, uv)
        | uu____45 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder) in
            let k' =
              let _0_238 = FStar_Syntax_Syntax.mk_Total k in
              FStar_Syntax_Util.arrow binders _0_238 in
            let uv =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k')))
                None r in
            let _0_239 =
              (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv, args)))
                (Some (k.FStar_Syntax_Syntax.n)) r in
            (_0_239, uv)
let mk_eq2:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____111 = FStar_Syntax_Util.type_u () in
        match uu____111 with
        | (t_type,u) ->
            let uu____116 =
              let _0_240 = FStar_TypeChecker_Env.all_binders env in
              new_uvar t1.FStar_Syntax_Syntax.pos _0_240 t_type in
            (match uu____116 with
             | (tt,uu____120) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
  FStar_Syntax_Syntax.term)
  | UNIV of (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe)
let uu___is_TERM: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____141 -> false
let __proj__TERM__item___0:
  uvi ->
    ((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0
let uu___is_UNIV: uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____167 -> false
let __proj__UNIV__item___0:
  uvi -> (FStar_Syntax_Syntax.universe_uvar* FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | UNIV _0 -> _0
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs;
  wl_deferred:
    (Prims.int* Prims.string* FStar_TypeChecker_Common.prob) Prims.list;
  ctr: Prims.int;
  defer_ok: Prims.bool;
  smt_ok: Prims.bool;
  tcenv: FStar_TypeChecker_Env.env;}
type solution =
  | Success of FStar_TypeChecker_Common.deferred
  | Failed of (FStar_TypeChecker_Common.prob* Prims.string)
let uu___is_Success: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____247 -> false
let __proj__Success__item___0: solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0
let uu___is_Failed: solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____261 -> false
let __proj__Failed__item___0:
  solution -> (FStar_TypeChecker_Common.prob* Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0
type variance =
  | COVARIANT
  | CONTRAVARIANT
  | INVARIANT
let uu___is_COVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____278 -> false
let uu___is_CONTRAVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____282 -> false
let uu___is_INVARIANT: variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____286 -> false
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string: FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___99_297  ->
    match uu___99_297 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
let term_to_string env t =
  let uu____310 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
  match uu____310 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t) ->
      let _0_242 = FStar_Syntax_Print.uvar_to_string u in
      let _0_241 = FStar_Syntax_Print.term_to_string t in
      FStar_Util.format2 "(%s:%s)" _0_242 _0_241
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____330;
         FStar_Syntax_Syntax.pos = uu____331;
         FStar_Syntax_Syntax.vars = uu____332;_},args)
      ->
      let _0_245 = FStar_Syntax_Print.uvar_to_string u in
      let _0_244 = FStar_Syntax_Print.term_to_string ty in
      let _0_243 = FStar_Syntax_Print.args_to_string args in
      FStar_Util.format3 "(%s:%s) %s" _0_245 _0_244 _0_243
  | uu____363 -> FStar_Syntax_Print.term_to_string t
let prob_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___100_369  ->
      match uu___100_369 with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_260 =
            let _0_259 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let _0_258 =
              let _0_257 = term_to_string env p.FStar_TypeChecker_Common.lhs in
              let _0_256 =
                let _0_255 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs in
                let _0_254 =
                  let _0_253 =
                    let _0_252 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs in
                    let _0_251 =
                      let _0_250 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs in
                      let _0_249 =
                        let _0_248 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (Prims.fst
                               p.FStar_TypeChecker_Common.logical_guard) in
                        let _0_247 =
                          let _0_246 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t") in
                          [_0_246] in
                        _0_248 :: _0_247 in
                      _0_250 :: _0_249 in
                    _0_252 :: _0_251 in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    _0_253 in
                _0_255 :: _0_254 in
              _0_257 :: _0_256 in
            _0_259 :: _0_258 in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            _0_260
      | FStar_TypeChecker_Common.CProb p ->
          let _0_262 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let _0_261 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _0_262
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_261
let uvi_to_string: FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___101_382  ->
      match uu___101_382 with
      | UNIV (u,t) ->
          let x =
            let uu____386 = FStar_Options.hide_uvar_nums () in
            if uu____386
            then "?"
            else
              (let _0_263 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right _0_263 FStar_Util.string_of_int) in
          let _0_264 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s %s" x _0_264
      | TERM ((u,uu____390),t) ->
          let x =
            let uu____395 = FStar_Options.hide_uvar_nums () in
            if uu____395
            then "?"
            else
              (let _0_265 = FStar_Unionfind.uvar_id u in
               FStar_All.pipe_right _0_265 FStar_Util.string_of_int) in
          let _0_266 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s %s" x _0_266
let uvis_to_string:
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let _0_267 = FStar_List.map (uvi_to_string env) uvis in
      FStar_All.pipe_right _0_267 (FStar_String.concat ", ")
let names_to_string: FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let _0_269 =
      let _0_268 = FStar_Util.set_elements nms in
      FStar_All.pipe_right _0_268
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right _0_269 (FStar_String.concat ", ")
let args_to_string args =
  let _0_270 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____437  ->
            match uu____437 with
            | (x,uu____441) -> FStar_Syntax_Print.term_to_string x)) in
  FStar_All.pipe_right _0_270 (FStar_String.concat " ")
let empty_worklist: FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let _0_271 = Prims.op_Negation (FStar_Options.eager_inference ()) in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = _0_271;
      smt_ok = true;
      tcenv = env
    }
let singleton':
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.bool -> worklist
  =
  fun env  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___127_457 = empty_worklist env in
        {
          attempting = [prob];
          wl_deferred = (uu___127_457.wl_deferred);
          ctr = (uu___127_457.ctr);
          defer_ok = (uu___127_457.defer_ok);
          smt_ok;
          tcenv = (uu___127_457.tcenv)
        }
let singleton:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true
let wl_of_guard env g =
  let uu___128_482 = empty_worklist env in
  let _0_272 = FStar_List.map Prims.snd g in
  {
    attempting = _0_272;
    wl_deferred = (uu___128_482.wl_deferred);
    ctr = (uu___128_482.ctr);
    defer_ok = false;
    smt_ok = (uu___128_482.smt_ok);
    tcenv = (uu___128_482.tcenv)
  }
let defer:
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___129_494 = wl in
        {
          attempting = (uu___129_494.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___129_494.ctr);
          defer_ok = (uu___129_494.defer_ok);
          smt_ok = (uu___129_494.smt_ok);
          tcenv = (uu___129_494.tcenv)
        }
let attempt: FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist
  =
  fun probs  ->
    fun wl  ->
      let uu___130_506 = wl in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___130_506.wl_deferred);
        ctr = (uu___130_506.ctr);
        defer_ok = (uu___130_506.defer_ok);
        smt_ok = (uu___130_506.smt_ok);
        tcenv = (uu___130_506.tcenv)
      }
let giveup:
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____517 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____517
         then
           let _0_273 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" reason _0_273
         else ());
        Failed (prob, reason)
let invert_rel: FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___102_521  ->
    match uu___102_521 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
let invert p =
  let uu___131_537 = p in
  {
    FStar_TypeChecker_Common.pid =
      (uu___131_537.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___131_537.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___131_537.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___131_537.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___131_537.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___131_537.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___131_537.FStar_TypeChecker_Common.rank)
  }
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p
let maybe_invert_p:
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___103_558  ->
    match uu___103_558 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_274  -> FStar_TypeChecker_Common.TProb _0_274)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_275  -> FStar_TypeChecker_Common.CProb _0_275)
let vary_rel:
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___104_574  ->
      match uu___104_574 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
let p_pid: FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___105_577  ->
    match uu___105_577 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let p_rel: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___106_586  ->
    match uu___106_586 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let p_reason: FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___107_596  ->
    match uu___107_596 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let p_loc: FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___108_606  ->
    match uu___108_606 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let p_guard:
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  =
  fun uu___109_617  ->
    match uu___109_617 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let p_scope: FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___110_628  ->
    match uu___110_628 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
let p_invert: FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___111_637  ->
    match uu___111_637 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_276  -> FStar_TypeChecker_Common.TProb _0_276) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_277  -> FStar_TypeChecker_Common.CProb _0_277) (invert p)
let is_top_level_prob: FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let _0_278 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    _0_278 = (Prims.parse_int "1")
let next_pid: Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0") in
  fun uu____659  -> FStar_Util.incr ctr; FStar_ST.read ctr
let mk_problem scope orig lhs rel rhs elt reason =
  let _0_280 = next_pid () in
  let _0_279 = new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = _0_280;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = _0_279;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  }
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env in
  let _0_282 = next_pid () in
  let _0_281 = new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0 in
  {
    FStar_TypeChecker_Common.pid = _0_282;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = _0_281;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  }
let problem_using_guard orig lhs rel rhs elt reason =
  let _0_283 = next_pid () in
  {
    FStar_TypeChecker_Common.pid = _0_283;
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
let explain:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____836 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel") in
        if uu____836
        then
          let _0_286 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let _0_285 = prob_to_string env d in
          let _0_284 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            _0_286 _0_285 _0_284 s
        else
          (let d = maybe_invert_p d in
           let rel =
             match p_rel d with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____841 -> failwith "impossible" in
           let uu____842 =
             match d with
             | FStar_TypeChecker_Common.TProb tp ->
                 let _0_288 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs in
                 let _0_287 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs in
                 (_0_288, _0_287)
             | FStar_TypeChecker_Common.CProb cp ->
                 let _0_290 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs in
                 let _0_289 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs in
                 (_0_290, _0_289) in
           match uu____842 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let commit: uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___112_861  ->
            match uu___112_861 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____868 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____871),t) -> FStar_Syntax_Util.set_uvar u t))
let find_term_uvar:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term Prims.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___113_894  ->
           match uu___113_894 with
           | UNIV uu____896 -> None
           | TERM ((u,uu____900),t) ->
               let uu____904 = FStar_Unionfind.equivalent uv u in
               if uu____904 then Some t else None)
let find_univ_uvar:
  FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe Prims.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___114_923  ->
           match uu___114_923 with
           | UNIV (u',t) ->
               let uu____927 = FStar_Unionfind.equivalent u u' in
               if uu____927 then Some t else None
           | uu____931 -> None)
let whnf:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      FStar_Syntax_Subst.compress
        (let _0_291 = FStar_Syntax_Util.unmeta t in
         FStar_TypeChecker_Normalize.normalize
           [FStar_TypeChecker_Normalize.Beta;
           FStar_TypeChecker_Normalize.WHNF] env _0_291)
let sn:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      FStar_Syntax_Subst.compress
        (FStar_TypeChecker_Normalize.normalize
           [FStar_TypeChecker_Normalize.Beta] env t)
let norm_arg env t =
  let _0_292 = sn env (Prims.fst t) in (_0_292, (Prims.snd t))
let sn_binders:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____978  ->
              match uu____978 with
              | (x,imp) ->
                  let _0_294 =
                    let uu___132_985 = x in
                    let _0_293 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___132_985.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___132_985.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = _0_293
                    } in
                  (_0_294, imp)))
let norm_univ:
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u =
        let u = FStar_Syntax_Subst.compress_univ u in
        match u with
        | FStar_Syntax_Syntax.U_succ u -> FStar_Syntax_Syntax.U_succ (aux u)
        | FStar_Syntax_Syntax.U_max us ->
            FStar_Syntax_Syntax.U_max (FStar_List.map aux us)
        | uu____1000 -> u in
      let _0_295 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _0_295
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0
let base_and_refinement env wl t1 =
  let rec aux norm t1 =
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1107 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t1 in
           match uu____1107 with
           | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,phi);
               FStar_Syntax_Syntax.tk = uu____1119;
               FStar_Syntax_Syntax.pos = uu____1120;
               FStar_Syntax_Syntax.vars = uu____1121;_} ->
               ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
           | tt ->
               failwith
                 (let _0_297 = FStar_Syntax_Print.term_to_string tt in
                  let _0_296 = FStar_Syntax_Print.tag_of_term tt in
                  FStar_Util.format2 "impossible: Got %s ... %s\n" _0_297
                    _0_296))
    | FStar_Syntax_Syntax.Tm_uinst _
      |FStar_Syntax_Syntax.Tm_fvar _|FStar_Syntax_Syntax.Tm_app _ ->
        if norm
        then (t1, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t1 in
           let uu____1176 =
             (FStar_Syntax_Subst.compress t1').FStar_Syntax_Syntax.n in
           match uu____1176 with
           | FStar_Syntax_Syntax.Tm_refine uu____1186 -> aux true t1'
           | uu____1191 -> (t1, None))
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _
       |FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_arrow _
          |FStar_Syntax_Syntax.Tm_abs _
           |FStar_Syntax_Syntax.Tm_uvar _
            |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
        -> (t1, None)
    | FStar_Syntax_Syntax.Tm_meta _
      |FStar_Syntax_Syntax.Tm_ascribed _
       |FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
        failwith
          (let _0_299 = FStar_Syntax_Print.term_to_string t1 in
           let _0_298 = FStar_Syntax_Print.tag_of_term t1 in
           FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _0_299
             _0_298) in
  let _0_300 = whnf env t1 in aux false _0_300
let unrefine:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let _0_302 =
        let _0_301 = empty_worklist env in base_and_refinement env _0_301 t in
      FStar_All.pipe_right _0_302 Prims.fst
let trivial_refinement:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let _0_303 = FStar_Syntax_Syntax.null_bv t in
    (_0_303, FStar_Syntax_Util.t_true)
let as_refinement env wl t =
  let uu____1283 = base_and_refinement env wl t in
  match uu____1283 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
let force_refinement uu____1342 =
  match uu____1342 with
  | (t_base,refopt) ->
      let uu____1356 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base in
      (match uu____1356 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
let wl_prob_to_string:
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___115_1380  ->
      match uu___115_1380 with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_306 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let _0_305 =
            FStar_Syntax_Print.term_to_string
              (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs) in
          let _0_304 =
            FStar_Syntax_Print.term_to_string
              (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs) in
          FStar_Util.format4 "%s: %s  (%s)  %s" _0_306 _0_305
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_304
      | FStar_TypeChecker_Common.CProb p ->
          let _0_309 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let _0_308 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs in
          let _0_307 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "%s: %s  (%s)  %s" _0_309 _0_308
            (rel_to_string p.FStar_TypeChecker_Common.relation) _0_307
let wl_to_string: worklist -> Prims.string =
  fun wl  ->
    let _0_312 =
      let _0_311 =
        let _0_310 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____1399  ->
                  match uu____1399 with | (uu____1403,uu____1404,x) -> x)) in
        FStar_List.append wl.attempting _0_310 in
      FStar_List.map (wl_prob_to_string wl) _0_311 in
    FStar_All.pipe_right _0_312 (FStar_String.concat "\n\t")
let u_abs:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____1421 =
          let uu____1431 =
            (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n in
          match uu____1431 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let _0_313 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), _0_313)
              else
                (let uu____1481 = FStar_Syntax_Util.abs_formals t in
                 match uu____1481 with
                 | (ys',t,uu____1502) ->
                     let _0_314 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t), _0_314))
          | uu____1530 ->
              let _0_316 =
                let _0_315 = FStar_Syntax_Syntax.mk_Total k in ([], _0_315) in
              ((ys, t), _0_316) in
        match uu____1421 with
        | ((ys,t),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys)
            then
              FStar_Syntax_Util.abs ys t
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c =
                 let _0_317 = FStar_Syntax_Util.rename_binders xs ys in
                 FStar_Syntax_Subst.subst_comp _0_317 c in
               let _0_321 =
                 let _0_320 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c)
                     (fun _0_318  -> FStar_Util.Inl _0_318) in
                 FStar_All.pipe_right _0_320 (fun _0_319  -> Some _0_319) in
               FStar_Syntax_Util.abs ys t _0_321)
let solve_prob':
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
              | Some phi -> phi in
            let uu____1630 = p_guard prob in
            match uu____1630 with
            | (uu____1633,uv) ->
                ((let uu____1636 =
                    (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n in
                  match uu____1636 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob in
                      let phi = u_abs k bs phi in
                      ((let uu____1654 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel") in
                        if uu____1654
                        then
                          let _0_324 = FStar_Util.string_of_int (p_pid prob) in
                          let _0_323 = FStar_Syntax_Print.term_to_string uv in
                          let _0_322 = FStar_Syntax_Print.term_to_string phi in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" _0_324 _0_323
                            _0_322
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi)
                  | uu____1658 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___133_1661 = wl in
                  {
                    attempting = (uu___133_1661.attempting);
                    wl_deferred = (uu___133_1661.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___133_1661.defer_ok);
                    smt_ok = (uu___133_1661.smt_ok);
                    tcenv = (uu___133_1661.tcenv)
                  }))
let extend_solution: Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____1674 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck") in
         if uu____1674
         then
           let _0_327 = FStar_Util.string_of_int pid in
           let _0_326 =
             let _0_325 = FStar_List.map (uvi_to_string wl.tcenv) sol in
             FStar_All.pipe_right _0_325 (FStar_String.concat ", ") in
           FStar_Util.print2 "Solving %s: with %s\n" _0_327 _0_326
         else ());
        commit sol;
        (let uu___134_1678 = wl in
         {
           attempting = (uu___134_1678.attempting);
           wl_deferred = (uu___134_1678.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___134_1678.defer_ok);
           smt_ok = (uu___134_1678.smt_ok);
           tcenv = (uu___134_1678.tcenv)
         })
let solve_prob:
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
            | (uu____1707,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t,FStar_TypeChecker_Common.NonTrivial f) ->
                Some (FStar_Syntax_Util.mk_conj t f) in
          (let uu____1718 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck") in
           if uu____1718
           then
             let _0_330 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let _0_329 =
               let _0_328 = FStar_List.map (uvi_to_string wl.tcenv) uvis in
               FStar_All.pipe_right _0_328 (FStar_String.concat ", ") in
             FStar_Util.print2 "Solving %s: with %s\n" _0_330 _0_329
           else ());
          solve_prob' false prob logical_guard uvis wl
let rec occurs wl uk t =
  let _0_332 =
    let _0_331 = FStar_Syntax_Free.uvars t in
    FStar_All.pipe_right _0_331 FStar_Util.set_elements in
  FStar_All.pipe_right _0_332
    (FStar_Util.for_some
       (fun uu____1759  ->
          match uu____1759 with
          | (uv,uu____1767) -> FStar_Unionfind.equivalent uv (Prims.fst uk)))
let occurs_check env wl uk t =
  let occurs_ok = Prims.op_Negation (occurs wl uk t) in
  let msg =
    if occurs_ok
    then None
    else
      Some
        ((let _0_334 = FStar_Syntax_Print.uvar_to_string (Prims.fst uk) in
          let _0_333 = FStar_Syntax_Print.term_to_string t in
          FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _0_334
            _0_333)) in
  (occurs_ok, msg)
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t in
  let uu____1865 = occurs_check env wl uk t in
  match uu____1865 with
  | (occurs_ok,msg) ->
      let _0_335 = FStar_Util.set_is_subset_of fvs_t fvs in
      (occurs_ok, _0_335, (msg, fvs, fvs_t))
let intersect_vars v1 v2 =
  let as_set v =
    FStar_All.pipe_right v
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (Prims.fst x) out)
         FStar_Syntax_Syntax.no_names) in
  let v1_set = as_set v1 in
  let uu____1945 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____1969  ->
            fun uu____1970  ->
              match (uu____1969, uu____1970) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2013 =
                    let _0_336 = FStar_Util.set_mem x v1_set in
                    FStar_All.pipe_left Prims.op_Negation _0_336 in
                  if uu____2013
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort in
                     let uu____2027 =
                       FStar_Util.set_is_subset_of fvs isect_set in
                     if uu____2027
                     then
                       let _0_337 = FStar_Util.set_add x isect_set in
                       (((x, imp) :: isect), _0_337)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names)) in
  match uu____1945 with | (isect,uu____2054) -> FStar_List.rev isect
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2103  ->
          fun uu____2104  ->
            match (uu____2103, uu____2104) with
            | ((a,uu____2114),(b,uu____2116)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let pat_var_opt env seen arg =
  let hd = norm_arg env arg in
  match (Prims.fst hd).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2160 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2166  ->
                match uu____2166 with
                | (b,uu____2170) -> FStar_Syntax_Syntax.bv_eq a b)) in
      if uu____2160 then None else Some (a, (Prims.snd hd))
  | uu____2179 -> None
let rec pat_vars:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders Prims.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd::rest ->
            let uu____2222 = pat_var_opt env seen hd in
            (match uu____2222 with
             | None  ->
                 ((let uu____2230 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel") in
                   if uu____2230
                   then
                     let _0_338 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (Prims.fst hd) in
                     FStar_Util.print1 "Not a pattern: %s\n" _0_338
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
let is_flex: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2242 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n in
    match uu____2242 with
    | FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar _;
         FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
         FStar_Syntax_Syntax.vars = _;_},_)
        -> true
    | uu____2256 -> false
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2318;
         FStar_Syntax_Syntax.pos = uu____2319;
         FStar_Syntax_Syntax.vars = uu____2320;_},args)
      -> (t, uv, k, args)
  | uu____2361 -> failwith "Not a flex-uvar"
let destruct_flex_pattern env t =
  let uu____2415 = destruct_flex_t t in
  match uu____2415 with
  | (t,uv,k,args) ->
      let uu____2483 = pat_vars env [] args in
      (match uu____2483 with
       | Some vars -> ((t, uv, k, args), (Some vars))
       | uu____2539 -> ((t, uv, k, args), None))
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth Prims.option*
  FStar_Syntax_Syntax.delta_depth Prims.option)
  | HeadMatch
  | FullMatch
let uu___is_MisMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____2587 -> false
let __proj__MisMatch__item___0:
  match_result ->
    (FStar_Syntax_Syntax.delta_depth Prims.option*
      FStar_Syntax_Syntax.delta_depth Prims.option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0
let uu___is_HeadMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____2610 -> false
let uu___is_FullMatch: match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____2614 -> false
let head_match: match_result -> match_result =
  fun uu___116_2617  ->
    match uu___116_2617 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____2626 -> HeadMatch
let fv_delta_depth:
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
let rec delta_depth_of_term:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth Prims.option
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta _|FStar_Syntax_Syntax.Tm_delayed _ ->
          failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown 
        |FStar_Syntax_Syntax.Tm_bvar _
         |FStar_Syntax_Syntax.Tm_name _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_let _|FStar_Syntax_Syntax.Tm_match _
          -> None
      | FStar_Syntax_Syntax.Tm_uinst (t,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t,_,_)
         |FStar_Syntax_Syntax.Tm_app (t,_)|FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
             FStar_Syntax_Syntax.sort = t;_},_)
          -> delta_depth_of_term env t
      | FStar_Syntax_Syntax.Tm_constant _
        |FStar_Syntax_Syntax.Tm_type _
         |FStar_Syntax_Syntax.Tm_arrow _|FStar_Syntax_Syntax.Tm_abs _ ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv -> Some (fv_delta_depth env fv)
let rec head_matches:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t1 = FStar_Syntax_Util.unmeta t1 in
        let t2 = FStar_Syntax_Util.unmeta t2 in
        match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____2716 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____2716
            then FullMatch
            else
              MisMatch
                ((Some (fv_delta_depth env f)),
                  (Some (fv_delta_depth env g)))
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____2721),FStar_Syntax_Syntax.Tm_uinst (g,uu____2723)) ->
            let _0_339 = head_matches env f g in
            FStar_All.pipe_right _0_339 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____2738),FStar_Syntax_Syntax.Tm_uvar (uv',uu____2740)) ->
            let uu____2765 = FStar_Unionfind.equivalent uv uv' in
            if uu____2765 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____2773),FStar_Syntax_Syntax.Tm_refine (y,uu____2775)) ->
            let _0_340 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right _0_340 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____2785),uu____2786) ->
            let _0_341 = head_matches env x.FStar_Syntax_Syntax.sort t2 in
            FStar_All.pipe_right _0_341 head_match
        | (uu____2791,FStar_Syntax_Syntax.Tm_refine (x,uu____2793)) ->
            let _0_342 = head_matches env t1 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right _0_342 head_match
        | (FStar_Syntax_Syntax.Tm_type _,FStar_Syntax_Syntax.Tm_type _)
          |(FStar_Syntax_Syntax.Tm_arrow _,FStar_Syntax_Syntax.Tm_arrow _) ->
            HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____2803),FStar_Syntax_Syntax.Tm_app (head',uu____2805))
            ->
            let _0_343 = head_matches env head head' in
            FStar_All.pipe_right _0_343 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____2835),uu____2836) ->
            let _0_344 = head_matches env head t2 in
            FStar_All.pipe_right _0_344 head_match
        | (uu____2851,FStar_Syntax_Syntax.Tm_app (head,uu____2853)) ->
            let _0_345 = head_matches env t1 head in
            FStar_All.pipe_right _0_345 head_match
        | uu____2868 ->
            MisMatch
              (let _0_347 = delta_depth_of_term env t1 in
               let _0_346 = delta_depth_of_term env t2 in (_0_347, _0_346))
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____2905 = FStar_Syntax_Util.head_and_args t in
    match uu____2905 with
    | (head,uu____2917) ->
        let uu____2932 =
          (FStar_Syntax_Util.un_uinst head).FStar_Syntax_Syntax.n in
        (match uu____2932 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____2935 =
               let _0_348 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               FStar_All.pipe_right _0_348 FStar_Option.isSome in
             if uu____2935
             then
               let _0_350 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t in
               FStar_All.pipe_right _0_350 (fun _0_349  -> Some _0_349)
             else None
         | uu____2948 -> None) in
  let success d r t1 t2 =
    (r, (if d > (Prims.parse_int "0") then Some (t1, t2) else None)) in
  let fail r = (r, None) in
  let rec aux retry n_delta t1 t2 =
    let r = head_matches env t1 t2 in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),_)|MisMatch
      (_,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3028 =
             let _0_352 = maybe_inline t1 in
             let _0_351 = maybe_inline t2 in (_0_352, _0_351) in
           match uu____3028 with
           | (None ,None ) -> fail r
           | (Some t1,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t1 t2
           | (None ,Some t2) ->
               aux false (n_delta + (Prims.parse_int "1")) t1 t2
           | (Some t1,Some t2) ->
               aux false (n_delta + (Prims.parse_int "1")) t1 t2)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3056 = FStar_TypeChecker_Common.decr_delta_depth d1 in
        (match uu____3056 with
         | None  -> fail r
         | Some d ->
             let t1 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t1 in
             let t2 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d;
                 FStar_TypeChecker_Normalize.WHNF] env wl t2 in
             aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
    | MisMatch (Some d1,Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
        let uu____3071 =
          if d1_greater_than_d2
          then
            let t1' =
              normalize_refinement
                [FStar_TypeChecker_Normalize.UnfoldUntil d2;
                FStar_TypeChecker_Normalize.WHNF] env wl t1 in
            (t1', t2)
          else
            (let t2' =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t2 in
             let _0_353 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t2 in
             (t1, _0_353)) in
        (match uu____3071 with
         | (t1,t2) -> aux retry (n_delta + (Prims.parse_int "1")) t1 t2)
    | MisMatch uu____3086 -> fail r
    | uu____3091 -> success n_delta r t1 t2 in
  aux true (Prims.parse_int "0") t1 t2
type tc =
  | T of (FStar_Syntax_Syntax.term*
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  | C of FStar_Syntax_Syntax.comp
let uu___is_T: tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3116 -> false
let __proj__T__item___0:
  tc ->
    (FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0
let uu___is_C: tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____3146 -> false
let __proj__C__item___0: tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0
type tcs = tc Prims.list
let generic_kind:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____3161 = FStar_Syntax_Util.type_u () in
      match uu____3161 with
      | (t,uu____3165) -> Prims.fst (new_uvar r binders t)
let kind_type:
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let _0_354 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right _0_354 Prims.fst
let rec decompose:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term)*
        (FStar_Syntax_Syntax.term -> Prims.bool)* (FStar_Syntax_Syntax.binder
        Prims.option* variance* tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t = FStar_Syntax_Util.unmeta t in
      let matches t' =
        let uu____3211 = head_matches env t t' in
        match uu____3211 with
        | MisMatch uu____3212 -> false
        | uu____3217 -> true in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd,args) ->
          let rebuild args' =
            let args =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____3277,imp),T (t,uu____3280)) -> (t, imp)
                     | uu____3297 -> failwith "Bad reconstruction") args
                args' in
            (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd, args)))
              None t.FStar_Syntax_Syntax.pos in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____3341  ->
                    match uu____3341 with
                    | (t,uu____3349) ->
                        (None, INVARIANT, (T (t, generic_kind))))) in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____3382 = failwith "Bad reconstruction" in
          let uu____3383 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____3383 with
           | (bs,c) ->
               let rebuild tcs =
                 let rec aux out bs tcs =
                   match (bs, tcs) with
                   | ((x,imp)::bs,(T (t,uu____3436))::tcs) ->
                       aux
                         (((let uu___135_3458 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___135_3458.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___135_3458.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }), imp) :: out) bs tcs
                   | ([],(C c)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c
                   | uu____3468 -> failwith "Bad reconstruction" in
                 aux [] bs tcs in
               let rec decompose out uu___117_3499 =
                 match uu___117_3499 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c)) :: out)
                 | hd::rest ->
                     decompose
                       (((Some hd), CONTRAVARIANT,
                          (T
                             (((Prims.fst hd).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest in
               let _0_355 = decompose [] bs in (rebuild, matches, _0_355))
      | uu____3582 ->
          let rebuild uu___118_3587 =
            match uu___118_3587 with
            | [] -> t
            | uu____3589 -> failwith "Bad reconstruction" in
          (rebuild, ((fun t  -> true)), [])
let un_T: tc -> FStar_Syntax_Syntax.term =
  fun uu___119_3608  ->
    match uu___119_3608 with
    | T (t,uu____3610) -> t
    | uu____3619 -> failwith "Impossible"
let arg_of_tc: tc -> FStar_Syntax_Syntax.arg =
  fun uu___120_3622  ->
    match uu___120_3622 with
    | T (t,uu____3624) -> FStar_Syntax_Syntax.as_arg t
    | uu____3633 -> failwith "Impossible"
let imitation_sub_probs orig env scope ps qs =
  let r = p_loc orig in
  let rel = p_rel orig in
  let sub_prob scope args q =
    match q with
    | (uu____3714,variance,T (ti,mk_kind)) ->
        let k = mk_kind scope r in
        let uu____3733 = new_uvar r scope k in
        (match uu____3733 with
         | (gi_xs,gi) ->
             let gi_ps =
               match args with
               | [] -> gi
               | uu____3745 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (gi, args)) None r in
             let _0_358 =
               let _0_357 =
                 mk_problem scope orig gi_ps (vary_rel rel variance) ti None
                   "type subterm" in
               FStar_All.pipe_left
                 (fun _0_356  -> FStar_TypeChecker_Common.TProb _0_356)
                 _0_357 in
             ((T (gi_xs, mk_kind)), _0_358))
    | (uu____3766,uu____3767,C uu____3768) -> failwith "impos" in
  let rec aux scope args qs =
    match qs with
    | [] -> ([], [], FStar_Syntax_Util.t_true)
    | q::qs ->
        let uu____3855 =
          match q with
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____3866;
               FStar_Syntax_Syntax.pos = uu____3867;
               FStar_Syntax_Syntax.vars = uu____3868;_})
              ->
              let uu____3883 =
                sub_prob scope args (bopt, variance, (T (ti, kind_type))) in
              (match uu____3883 with
               | (T (gi_xs,uu____3899),prob) ->
                   let _0_361 =
                     let _0_360 = FStar_Syntax_Syntax.mk_Total' gi_xs uopt in
                     FStar_All.pipe_left (fun _0_359  -> C _0_359) _0_360 in
                   (_0_361, [prob])
               | uu____3910 -> failwith "impossible")
          | (bopt,variance,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti,uopt);
               FStar_Syntax_Syntax.tk = uu____3920;
               FStar_Syntax_Syntax.pos = uu____3921;
               FStar_Syntax_Syntax.vars = uu____3922;_})
              ->
              let uu____3937 =
                sub_prob scope args (bopt, variance, (T (ti, kind_type))) in
              (match uu____3937 with
               | (T (gi_xs,uu____3953),prob) ->
                   let _0_364 =
                     let _0_363 = FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt in
                     FStar_All.pipe_left (fun _0_362  -> C _0_362) _0_363 in
                   (_0_364, [prob])
               | uu____3964 -> failwith "impossible")
          | (uu____3970,uu____3971,C
             { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
               FStar_Syntax_Syntax.tk = uu____3973;
               FStar_Syntax_Syntax.pos = uu____3974;
               FStar_Syntax_Syntax.vars = uu____3975;_})
              ->
              let components =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  (FStar_List.map
                     (fun t  ->
                        (None, INVARIANT, (T ((Prims.fst t), generic_kind))))) in
              let components =
                (None, COVARIANT,
                  (T ((c.FStar_Syntax_Syntax.result_typ), kind_type)))
                :: components in
              let uu____4049 =
                let _0_365 = FStar_List.map (sub_prob scope args) components in
                FStar_All.pipe_right _0_365 FStar_List.unzip in
              (match uu____4049 with
               | (tcs,sub_probs) ->
                   let gi_xs =
                     let _0_370 =
                       let _0_369 =
                         let _0_366 = FStar_List.hd tcs in
                         FStar_All.pipe_right _0_366 un_T in
                       let _0_368 =
                         let _0_367 = FStar_List.tl tcs in
                         FStar_All.pipe_right _0_367
                           (FStar_List.map arg_of_tc) in
                       {
                         FStar_Syntax_Syntax.comp_univs =
                           (c.FStar_Syntax_Syntax.comp_univs);
                         FStar_Syntax_Syntax.effect_name =
                           (c.FStar_Syntax_Syntax.effect_name);
                         FStar_Syntax_Syntax.result_typ = _0_369;
                         FStar_Syntax_Syntax.effect_args = _0_368;
                         FStar_Syntax_Syntax.flags =
                           (c.FStar_Syntax_Syntax.flags)
                       } in
                     FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _0_370 in
                   ((C gi_xs), sub_probs))
          | uu____4082 ->
              let uu____4089 = sub_prob scope args q in
              (match uu____4089 with | (ktec,prob) -> (ktec, [prob])) in
        (match uu____3855 with
         | (tc,probs) ->
             let uu____4107 =
               match q with
               | (Some b,uu____4133,uu____4134) ->
                   let _0_372 =
                     let _0_371 = FStar_Syntax_Util.arg_of_non_null_binder b in
                     _0_371 :: args in
                   ((Some b), (b :: scope), _0_372)
               | uu____4157 -> (None, scope, args) in
             (match uu____4107 with
              | (bopt,scope,args) ->
                  let uu____4200 = aux scope args qs in
                  (match uu____4200 with
                   | (sub_probs,tcs,f) ->
                       let f =
                         match bopt with
                         | None  ->
                             FStar_Syntax_Util.mk_conj_l
                               (let _0_373 =
                                  FStar_All.pipe_right probs
                                    (FStar_List.map
                                       (fun prob  ->
                                          FStar_All.pipe_right (p_guard prob)
                                            Prims.fst)) in
                                f :: _0_373)
                         | Some b ->
                             FStar_Syntax_Util.mk_conj_l
                               (let _0_375 =
                                  FStar_Syntax_Util.mk_forall (Prims.fst b) f in
                                let _0_374 =
                                  FStar_All.pipe_right probs
                                    (FStar_List.map
                                       (fun prob  ->
                                          FStar_All.pipe_right (p_guard prob)
                                            Prims.fst)) in
                                _0_375 :: _0_374) in
                       ((FStar_List.append probs sub_probs), (tc :: tcs), f)))) in
  aux scope ps qs
type flex_t =
  (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.uvar*
    FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.args)
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar* FStar_Syntax_Syntax.typ)*
    FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)*
    FStar_Syntax_Syntax.arg Prims.list*
    ((tc Prims.list -> FStar_Syntax_Syntax.typ)*
    (FStar_Syntax_Syntax.typ -> Prims.bool)* (FStar_Syntax_Syntax.binder
    Prims.option* variance* tc) Prims.list))
let rigid_rigid: Prims.int = Prims.parse_int "0"
let flex_rigid_eq: Prims.int = Prims.parse_int "1"
let flex_refine_inner: Prims.int = Prims.parse_int "2"
let flex_refine: Prims.int = Prims.parse_int "3"
let flex_rigid: Prims.int = Prims.parse_int "4"
let rigid_flex: Prims.int = Prims.parse_int "5"
let refine_flex: Prims.int = Prims.parse_int "6"
let flex_flex: Prims.int = Prims.parse_int "7"
let compress_tprob wl p =
  let uu___136_4282 = p in
  let _0_377 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs in
  let _0_376 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs in
  {
    FStar_TypeChecker_Common.pid =
      (uu___136_4282.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = _0_377;
    FStar_TypeChecker_Common.relation =
      (uu___136_4282.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = _0_376;
    FStar_TypeChecker_Common.element =
      (uu___136_4282.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___136_4282.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___136_4282.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___136_4282.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___136_4282.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___136_4282.FStar_TypeChecker_Common.rank)
  }
let compress_prob:
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p ->
          let _0_379 = compress_tprob wl p in
          FStar_All.pipe_right _0_379
            (fun _0_378  -> FStar_TypeChecker_Common.TProb _0_378)
      | FStar_TypeChecker_Common.CProb uu____4296 -> p
let rank:
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int* FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let _0_380 = compress_prob wl pr in
        FStar_All.pipe_right _0_380 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____4315 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____4315 with
           | (lh,uu____4328) ->
               let uu____4343 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____4343 with
                | (rh,uu____4356) ->
                    let uu____4371 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____4380,FStar_Syntax_Syntax.Tm_uvar uu____4381)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar _,_)
                        |(_,FStar_Syntax_Syntax.Tm_uvar _) when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____4406,uu____4407)
                          ->
                          let uu____4416 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs in
                          (match uu____4416 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____4456 ->
                                    let rank =
                                      let uu____4463 = is_top_level_prob prob in
                                      if uu____4463
                                      then flex_refine
                                      else flex_refine_inner in
                                    let _0_382 =
                                      let uu___137_4467 = tp in
                                      let _0_381 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___137_4467.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___137_4467.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___137_4467.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs = _0_381;
                                        FStar_TypeChecker_Common.element =
                                          (uu___137_4467.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___137_4467.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___137_4467.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___137_4467.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___137_4467.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___137_4467.FStar_TypeChecker_Common.rank)
                                      } in
                                    (rank, _0_382)))
                      | (uu____4477,FStar_Syntax_Syntax.Tm_uvar uu____4478)
                          ->
                          let uu____4487 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs in
                          (match uu____4487 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____4527 ->
                                    let _0_384 =
                                      let uu___138_4537 = tp in
                                      let _0_383 =
                                        force_refinement (b, ref_opt) in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___138_4537.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs = _0_383;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___138_4537.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___138_4537.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___138_4537.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___138_4537.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___138_4537.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___138_4537.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___138_4537.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___138_4537.FStar_TypeChecker_Common.rank)
                                      } in
                                    (refine_flex, _0_384)))
                      | (uu____4549,uu____4550) -> (rigid_rigid, tp) in
                    (match uu____4371 with
                     | (rank,tp) ->
                         let _0_386 =
                           FStar_All.pipe_right
                             (let uu___139_4563 = tp in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___139_4563.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___139_4563.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___139_4563.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___139_4563.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___139_4563.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___139_4563.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___139_4563.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___139_4563.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___139_4563.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_385  ->
                                FStar_TypeChecker_Common.TProb _0_385) in
                         (rank, _0_386))))
      | FStar_TypeChecker_Common.CProb cp ->
          let _0_388 =
            FStar_All.pipe_right
              (let uu___140_4571 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___140_4571.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___140_4571.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___140_4571.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___140_4571.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___140_4571.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___140_4571.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___140_4571.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___140_4571.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___140_4571.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_387  -> FStar_TypeChecker_Common.CProb _0_387) in
          (rigid_rigid, _0_388)
let next_prob:
  worklist ->
    (FStar_TypeChecker_Common.prob Prims.option*
      FStar_TypeChecker_Common.prob Prims.list* Prims.int)
  =
  fun wl  ->
    let rec aux uu____4603 probs =
      match uu____4603 with
      | (min_rank,min,out) ->
          (match probs with
           | [] -> (min, out, min_rank)
           | hd::tl ->
               let uu____4633 = rank wl hd in
               (match uu____4633 with
                | (rank,hd) ->
                    if rank <= flex_rigid_eq
                    then
                      (match min with
                       | None  ->
                           ((Some hd), (FStar_List.append out tl), rank)
                       | Some m ->
                           ((Some hd), (FStar_List.append out (m :: tl)),
                             rank))
                    else
                      if rank < min_rank
                      then
                        (match min with
                         | None  -> aux (rank, (Some hd), out) tl
                         | Some m -> aux (rank, (Some hd), (m :: out)) tl)
                      else aux (min_rank, min, (hd :: out)) tl)) in
    aux ((flex_flex + (Prims.parse_int "1")), None, []) wl.attempting
let is_flex_rigid: Prims.int -> Prims.bool =
  fun rank  -> (flex_refine_inner <= rank) && (rank <= flex_rigid)
let is_rigid_flex: Prims.int -> Prims.bool =
  fun rank  -> (rigid_flex <= rank) && (rank <= refine_flex)
type univ_eq_sol =
  | UDeferred of worklist
  | USolved of worklist
  | UFailed of Prims.string
let uu___is_UDeferred: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____4698 -> false
let __proj__UDeferred__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0
let uu___is_USolved: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____4710 -> false
let __proj__USolved__item___0: univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0
let uu___is_UFailed: univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____4722 -> false
let __proj__UFailed__item___0: univ_eq_sol -> Prims.string =
  fun projectee  -> match projectee with | UFailed _0 -> _0
let rec really_solve_universe_eq:
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u1 = FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1 in
          let u2 = FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2 in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u  ->
                        let uu____4759 = FStar_Syntax_Util.univ_kernel u in
                        match uu____4759 with
                        | (k,uu____4763) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____4768 -> false)))
            | uu____4769 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let try_umax_components u1 u2 msg =
            match (u1, u2) with
            | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2)
                ->
                if (FStar_List.length us1) = (FStar_List.length us2)
                then
                  let rec aux wl us1 us2 =
                    match (us1, us2) with
                    | (u1::us1,u2::us2) ->
                        let uu____4812 =
                          really_solve_universe_eq pid_orig wl u1 u2 in
                        (match uu____4812 with
                         | USolved wl -> aux wl us1 us2
                         | failed -> failed)
                    | uu____4815 -> USolved wl in
                  aux wl us1 us2
                else
                  UFailed
                    ((let _0_390 = FStar_Syntax_Print.univ_to_string u1 in
                      let _0_389 = FStar_Syntax_Print.univ_to_string u2 in
                      FStar_Util.format2
                        "Unable to unify universes: %s and %s" _0_390 _0_389))
            | (FStar_Syntax_Syntax.U_max us,u')
              |(u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl us =
                  match us with
                  | [] -> USolved wl
                  | u::us ->
                      let uu____4837 =
                        really_solve_universe_eq pid_orig wl u u' in
                      (match uu____4837 with
                       | USolved wl -> aux wl us
                       | failed -> failed) in
                aux wl us
            | uu____4840 ->
                UFailed
                  (let _0_392 = FStar_Syntax_Print.univ_to_string u1 in
                   let _0_391 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format3
                     "Unable to unify universes: %s and %s (%s)" _0_392
                     _0_391 msg) in
          match (u1, u2) with
          | (FStar_Syntax_Syntax.U_bvar _,_)
            |(FStar_Syntax_Syntax.U_unknown ,_)
             |(_,FStar_Syntax_Syntax.U_bvar _)
              |(_,FStar_Syntax_Syntax.U_unknown ) ->
              failwith
                (let _0_394 = FStar_Syntax_Print.univ_to_string u1 in
                 let _0_393 = FStar_Syntax_Print.univ_to_string u2 in
                 FStar_Util.format2
                   "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                   _0_394 _0_393)
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u1,FStar_Syntax_Syntax.U_succ u2) ->
              really_solve_universe_eq pid_orig wl u1 u2
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____4860 = FStar_Unionfind.equivalent v1 v2 in
              if uu____4860
              then USolved wl
              else
                (let wl = extend_solution pid_orig [UNIV (v1, u2)] wl in
                 USolved wl)
          | (FStar_Syntax_Syntax.U_unif v1,u)
            |(u,FStar_Syntax_Syntax.U_unif v1) ->
              let u = norm_univ wl u in
              let uu____4873 = occurs_univ v1 u in
              if uu____4873
              then
                let _0_397 =
                  let _0_396 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let _0_395 = FStar_Syntax_Print.univ_to_string u in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    _0_396 _0_395 in
                try_umax_components u1 u2 _0_397
              else USolved (extend_solution pid_orig [UNIV (v1, u)] wl)
          | (FStar_Syntax_Syntax.U_max _,_)|(_,FStar_Syntax_Syntax.U_max _)
              ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u1 = norm_univ wl u1 in
                 let u2 = norm_univ wl u2 in
                 let uu____4884 = FStar_Syntax_Util.eq_univs u1 u2 in
                 if uu____4884
                 then USolved wl
                 else try_umax_components u1 u2 "")
          | (FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_zero )
            |(FStar_Syntax_Syntax.U_succ _,FStar_Syntax_Syntax.U_name _)
             |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ _)
              |(FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name _)
               |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_succ _)
                |(FStar_Syntax_Syntax.U_name _,FStar_Syntax_Syntax.U_zero )
              -> UFailed "Incompatible universes"
let solve_universe_eq:
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
  let uu____4955 = bc1 in
  match uu____4955 with
  | (bs1,mk_cod1) ->
      let uu____4980 = bc2 in
      (match uu____4980 with
       | (bs2,mk_cod2) ->
           let curry n bs mk_cod =
             let uu____5027 = FStar_Util.first_N n bs in
             match uu____5027 with
             | (bs,rest) -> let _0_398 = mk_cod rest in (bs, _0_398) in
           let l1 = FStar_List.length bs1 in
           let l2 = FStar_List.length bs2 in
           if l1 = l2
           then
             let _0_402 = let _0_399 = mk_cod1 [] in (bs1, _0_399) in
             let _0_401 = let _0_400 = mk_cod2 [] in (bs2, _0_400) in
             (_0_402, _0_401)
           else
             if l1 > l2
             then
               (let _0_405 = curry l2 bs1 mk_cod1 in
                let _0_404 = let _0_403 = mk_cod2 [] in (bs2, _0_403) in
                (_0_405, _0_404))
             else
               (let _0_408 = let _0_406 = mk_cod1 [] in (bs1, _0_406) in
                let _0_407 = curry l1 bs2 mk_cod2 in (_0_408, _0_407)))
let rec solve: FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____5192 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____5192
       then
         let _0_409 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" _0_409
       else ());
      (let uu____5194 = next_prob probs in
       match uu____5194 with
       | (Some hd,tl,rank) ->
           let probs =
             let uu___141_5207 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___141_5207.wl_deferred);
               ctr = (uu___141_5207.ctr);
               defer_ok = (uu___141_5207.defer_ok);
               smt_ok = (uu___141_5207.smt_ok);
               tcenv = (uu___141_5207.tcenv)
             } in
           (match hd with
            | FStar_TypeChecker_Common.CProb cp ->
                solve_c env (maybe_invert cp) probs
            | FStar_TypeChecker_Common.TProb tp ->
                if
                  ((Prims.op_Negation probs.defer_ok) &&
                     (flex_refine_inner <= rank))
                    && (rank <= flex_rigid)
                then
                  let uu____5214 = solve_flex_rigid_join env tp probs in
                  (match uu____5214 with
                   | None  -> solve_t' env (maybe_invert tp) probs
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs.defer_ok) &&
                       (rigid_flex <= rank))
                      && (rank <= refine_flex)
                  then
                    (let uu____5218 = solve_rigid_flex_meet env tp probs in
                     match uu____5218 with
                     | None  -> solve_t' env (maybe_invert tp) probs
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs)
       | (None ,uu____5222,uu____5223) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____5232 ->
                let uu____5237 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____5265  ->
                          match uu____5265 with
                          | (c,uu____5270,uu____5271) -> c < probs.ctr)) in
                (match uu____5237 with
                 | (attempt,rest) ->
                     (match attempt with
                      | [] ->
                          Success
                            (FStar_List.map
                               (fun uu____5298  ->
                                  match uu____5298 with
                                  | (uu____5304,x,y) -> (x, y))
                               probs.wl_deferred)
                      | uu____5307 ->
                          let _0_411 =
                            let uu___142_5312 = probs in
                            let _0_410 =
                              FStar_All.pipe_right attempt
                                (FStar_List.map
                                   (fun uu____5321  ->
                                      match uu____5321 with
                                      | (uu____5325,uu____5326,y) -> y)) in
                            {
                              attempting = _0_410;
                              wl_deferred = rest;
                              ctr = (uu___142_5312.ctr);
                              defer_ok = (uu___142_5312.defer_ok);
                              smt_ok = (uu___142_5312.smt_ok);
                              tcenv = (uu___142_5312.tcenv)
                            } in
                          solve env _0_411))))
and solve_one_universe_eq:
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
            let uu____5333 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____5333 with
            | USolved wl ->
                let _0_412 = solve_prob orig None [] wl in solve env _0_412
            | UFailed msg -> giveup env msg orig
            | UDeferred wl -> solve env (defer "" orig wl)
and solve_maybe_uinsts:
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
            let rec aux wl us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl
              | (u1::us1,u2::us2) ->
                  let uu____5368 = solve_universe_eq (p_pid orig) wl u1 u2 in
                  (match uu____5368 with
                   | USolved wl -> aux wl us1 us2
                   | failed_or_deferred -> failed_or_deferred)
              | uu____5371 -> UFailed "Unequal number of universes" in
            let t1 = whnf env t1 in
            let t2 = whnf env t2 in
            match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____5379;
                  FStar_Syntax_Syntax.pos = uu____5380;
                  FStar_Syntax_Syntax.vars = uu____5381;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____5384;
                  FStar_Syntax_Syntax.pos = uu____5385;
                  FStar_Syntax_Syntax.vars = uu____5386;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst _,_)
              |(_,FStar_Syntax_Syntax.Tm_uinst _) ->
                failwith "Impossible: expect head symbols to match"
            | uu____5402 -> USolved wl
and giveup_or_defer:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> Prims.string -> solution
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____5410 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____5410
              then
                let _0_413 = prob_to_string env orig in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  _0_413 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig
and solve_rigid_flex_meet:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____5418 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____5418
         then
           let _0_414 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             _0_414
         else ());
        (let uu____5420 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs in
         match uu____5420 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____5462 = head_matches_delta env () t1 t2 in
               match uu____5462 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____5484 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t1,t2) -> Some (t1, []))
                    | HeadMatch  ->
                        let uu____5510 =
                          match ts with
                          | Some (t1,t2) ->
                              let _0_416 = FStar_Syntax_Subst.compress t1 in
                              let _0_415 = FStar_Syntax_Subst.compress t2 in
                              (_0_416, _0_415)
                          | None  ->
                              let _0_418 = FStar_Syntax_Subst.compress t1 in
                              let _0_417 = FStar_Syntax_Subst.compress t2 in
                              (_0_418, _0_417) in
                        (match uu____5510 with
                         | (t1,t2) ->
                             let eq_prob t1 t2 =
                               let _0_420 =
                                 new_problem env t1
                                   FStar_TypeChecker_Common.EQ t2 None
                                   t1.FStar_Syntax_Syntax.pos
                                   "meeting refinements" in
                               FStar_All.pipe_left
                                 (fun _0_419  ->
                                    FStar_TypeChecker_Common.TProb _0_419)
                                 _0_420 in
                             (match ((t1.FStar_Syntax_Syntax.n),
                                      (t2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  Some
                                    (let _0_424 =
                                       (FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_refine
                                             (let _0_421 =
                                                FStar_Syntax_Util.mk_disj
                                                  phi1 phi2 in
                                              (x, _0_421)))) None
                                         t1.FStar_Syntax_Syntax.pos in
                                     let _0_423 =
                                       let _0_422 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           y.FStar_Syntax_Syntax.sort in
                                       [_0_422] in
                                     (_0_424, _0_423))
                              | (uu____5584,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5586)) ->
                                  Some
                                    (let _0_426 =
                                       let _0_425 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           t1 in
                                       [_0_425] in
                                     (t1, _0_426))
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____5596),uu____5597) ->
                                  Some
                                    (let _0_428 =
                                       let _0_427 =
                                         eq_prob x.FStar_Syntax_Syntax.sort
                                           t2 in
                                       [_0_427] in
                                     (t2, _0_428))
                              | uu____5606 ->
                                  let uu____5609 =
                                    FStar_Syntax_Util.head_and_args t1 in
                                  (match uu____5609 with
                                   | (head1,uu____5624) ->
                                       let uu____5639 =
                                         (FStar_Syntax_Util.un_uinst head1).FStar_Syntax_Syntax.n in
                                       (match uu____5639 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____5644;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____5646;_}
                                            ->
                                            let prev =
                                              if i > (Prims.parse_int "1")
                                              then
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                  (i - (Prims.parse_int "1"))
                                              else
                                                FStar_Syntax_Syntax.Delta_constant in
                                            let t1 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t1 in
                                            let t2 =
                                              FStar_TypeChecker_Normalize.normalize
                                                [FStar_TypeChecker_Normalize.WHNF;
                                                FStar_TypeChecker_Normalize.UnfoldUntil
                                                  prev] env t2 in
                                            disjoin t1 t2
                                        | uu____5655 -> None))))) in
             let tt = u in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5664) ->
                  let uu____5677 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___121_5686  ->
                            match uu___121_5686 with
                            | FStar_TypeChecker_Common.TProb tp ->
                                (match tp.FStar_TypeChecker_Common.rank with
                                 | Some rank when is_rigid_flex rank ->
                                     let uu____5691 =
                                       FStar_Syntax_Util.head_and_args
                                         tp.FStar_TypeChecker_Common.rhs in
                                     (match uu____5691 with
                                      | (u',uu____5702) ->
                                          let uu____5717 =
                                            (whnf env u').FStar_Syntax_Syntax.n in
                                          (match uu____5717 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____5719) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____5735 -> false))
                                 | uu____5736 -> false)
                            | uu____5738 -> false)) in
                  (match uu____5677 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____5759 tps =
                         match uu____5759 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd)::tl ->
                                  let uu____5786 =
                                    let _0_429 =
                                      whnf env
                                        hd.FStar_TypeChecker_Common.lhs in
                                    disjoin bound _0_429 in
                                  (match uu____5786 with
                                   | Some (bound,sub) ->
                                       make_lower_bound
                                         (bound,
                                           (FStar_List.append sub sub_probs))
                                         tl
                                   | None  -> None)
                              | uu____5809 -> None) in
                       let uu____5814 =
                         let _0_431 =
                           let _0_430 =
                             whnf env tp.FStar_TypeChecker_Common.lhs in
                           (_0_430, []) in
                         make_lower_bound _0_431 lower_bounds in
                       (match uu____5814 with
                        | None  ->
                            ((let uu____5825 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____5825
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
                                "meeting refinements" in
                            ((let uu____5838 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck") in
                              if uu____5838
                              then
                                let wl' =
                                  let uu___143_5840 = wl in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___143_5840.wl_deferred);
                                    ctr = (uu___143_5840.ctr);
                                    defer_ok = (uu___143_5840.defer_ok);
                                    smt_ok = (uu___143_5840.smt_ok);
                                    tcenv = (uu___143_5840.tcenv)
                                  } in
                                let _0_432 = wl_to_string wl' in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n" _0_432
                              else ());
                             (let uu____5842 =
                                solve_t env eq_prob
                                  (let uu___144_5843 = wl in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___144_5843.wl_deferred);
                                     ctr = (uu___144_5843.ctr);
                                     defer_ok = (uu___144_5843.defer_ok);
                                     smt_ok = (uu___144_5843.smt_ok);
                                     tcenv = (uu___144_5843.tcenv)
                                   }) in
                              match uu____5842 with
                              | Success uu____5845 ->
                                  let wl =
                                    let uu___145_5847 = wl in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___145_5847.wl_deferred);
                                      ctr = (uu___145_5847.ctr);
                                      defer_ok = (uu___145_5847.defer_ok);
                                      smt_ok = (uu___145_5847.smt_ok);
                                      tcenv = (uu___145_5847.tcenv)
                                    } in
                                  let wl =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl in
                                  let uu____5849 =
                                    FStar_List.fold_left
                                      (fun wl  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl) wl
                                      lower_bounds in
                                  Some wl
                              | uu____5852 -> None))))
              | uu____5853 -> failwith "Impossible: Not a rigid-flex"))
and solve_flex_rigid_join:
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist Prims.option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____5860 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck") in
         if uu____5860
         then
           let _0_433 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             _0_433
         else ());
        (let uu____5862 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
         match uu____5862 with
         | (u,args) ->
             let uu____5889 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4")) in
             (match uu____5889 with
              | (ok,head_match,partial_match,fallback,failed_match) ->
                  let max i j = if i < j then j else i in
                  let base_types_match t1 t2 =
                    let uu____5920 = FStar_Syntax_Util.head_and_args t1 in
                    match uu____5920 with
                    | (h1,args1) ->
                        let uu____5948 = FStar_Syntax_Util.head_and_args t2 in
                        (match uu____5948 with
                         | (h2,uu____5961) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____5980 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2 in
                                  if uu____5980
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       Some
                                         ((let _0_436 =
                                             let _0_435 =
                                               new_problem env t1
                                                 FStar_TypeChecker_Common.EQ
                                                 t2 None
                                                 t1.FStar_Syntax_Syntax.pos
                                                 "joining refinements" in
                                             FStar_All.pipe_left
                                               (fun _0_434  ->
                                                  FStar_TypeChecker_Common.TProb
                                                    _0_434) _0_435 in
                                           [_0_436])))
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
                                       Some
                                         ((let _0_439 =
                                             let _0_438 =
                                               new_problem env t1
                                                 FStar_TypeChecker_Common.EQ
                                                 t2 None
                                                 t1.FStar_Syntax_Syntax.pos
                                                 "joining refinements" in
                                             FStar_All.pipe_left
                                               (fun _0_437  ->
                                                  FStar_TypeChecker_Common.TProb
                                                    _0_437) _0_438 in
                                           [_0_439])))
                                  else None
                              | uu____6017 -> None)) in
                  let conjoin t1 t2 =
                    match ((t1.FStar_Syntax_Syntax.n),
                            (t2.FStar_Syntax_Syntax.n))
                    with
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,phi1),FStar_Syntax_Syntax.Tm_refine (y,phi2)) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort
                            y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m ->
                             let x = FStar_Syntax_Syntax.freshen_bv x in
                             let subst =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x)] in
                             let phi1 = FStar_Syntax_Subst.subst subst phi1 in
                             let phi2 = FStar_Syntax_Subst.subst subst phi2 in
                             Some
                               (let _0_441 =
                                  let _0_440 =
                                    FStar_Syntax_Util.mk_conj phi1 phi2 in
                                  FStar_Syntax_Util.refine x _0_440 in
                                (_0_441, m)))
                    | (uu____6091,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____6093)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort in
                        (match m with
                         | None  -> None
                         | Some m -> Some (t2, m))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____6125),uu____6126) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2 in
                        (match m with
                         | None  -> None
                         | Some m -> Some (t1, m))
                    | uu____6157 ->
                        let m = base_types_match t1 t2 in
                        (match m with
                         | None  -> None
                         | Some m -> Some (t1, m)) in
                  let tt = u in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6191) ->
                       let uu____6204 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___122_6213  ->
                                 match uu___122_6213 with
                                 | FStar_TypeChecker_Common.TProb tp ->
                                     (match tp.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank when is_flex_rigid rank ->
                                          let uu____6218 =
                                            FStar_Syntax_Util.head_and_args
                                              tp.FStar_TypeChecker_Common.lhs in
                                          (match uu____6218 with
                                           | (u',uu____6229) ->
                                               let uu____6244 =
                                                 (whnf env u').FStar_Syntax_Syntax.n in
                                               (match uu____6244 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____6246) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____6262 -> false))
                                      | uu____6263 -> false)
                                 | uu____6265 -> false)) in
                       (match uu____6204 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____6290 tps =
                              match uu____6290 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb hd)::tl
                                       ->
                                       let uu____6331 =
                                         let _0_442 =
                                           whnf env
                                             hd.FStar_TypeChecker_Common.rhs in
                                         conjoin bound _0_442 in
                                       (match uu____6331 with
                                        | Some (bound,sub) ->
                                            make_upper_bound
                                              (bound,
                                                (FStar_List.append sub
                                                   sub_probs)) tl
                                        | None  -> None)
                                   | uu____6370 -> None) in
                            let uu____6377 =
                              let _0_444 =
                                let _0_443 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs in
                                (_0_443, []) in
                              make_upper_bound _0_444 upper_bounds in
                            (match uu____6377 with
                             | None  ->
                                 ((let uu____6392 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____6392
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
                                     "joining refinements" in
                                 ((let uu____6411 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck") in
                                   if uu____6411
                                   then
                                     let wl' =
                                       let uu___146_6413 = wl in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___146_6413.wl_deferred);
                                         ctr = (uu___146_6413.ctr);
                                         defer_ok = (uu___146_6413.defer_ok);
                                         smt_ok = (uu___146_6413.smt_ok);
                                         tcenv = (uu___146_6413.tcenv)
                                       } in
                                     let _0_445 = wl_to_string wl' in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       _0_445
                                   else ());
                                  (let uu____6415 =
                                     solve_t env eq_prob
                                       (let uu___147_6416 = wl in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___147_6416.wl_deferred);
                                          ctr = (uu___147_6416.ctr);
                                          defer_ok = (uu___147_6416.defer_ok);
                                          smt_ok = (uu___147_6416.smt_ok);
                                          tcenv = (uu___147_6416.tcenv)
                                        }) in
                                   match uu____6415 with
                                   | Success uu____6418 ->
                                       let wl =
                                         let uu___148_6420 = wl in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___148_6420.wl_deferred);
                                           ctr = (uu___148_6420.ctr);
                                           defer_ok =
                                             (uu___148_6420.defer_ok);
                                           smt_ok = (uu___148_6420.smt_ok);
                                           tcenv = (uu___148_6420.tcenv)
                                         } in
                                       let wl =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl in
                                       let uu____6422 =
                                         FStar_List.fold_left
                                           (fun wl  ->
                                              fun p  ->
                                                solve_prob' true p None [] wl)
                                           wl upper_bounds in
                                       Some wl
                                   | uu____6425 -> None))))
                   | uu____6426 -> failwith "Impossible: Not a flex-rigid")))
and solve_binders:
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
              let rec aux scope env subst xs ys =
                match (xs, ys) with
                | ([],[]) ->
                    let rhs_prob = rhs (FStar_List.rev scope) env subst in
                    ((let uu____6491 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____6491
                      then
                        let _0_446 = prob_to_string env rhs_prob in
                        FStar_Util.print1 "rhs_prob = %s\n" _0_446
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob) Prims.fst in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs,(hd2,imp')::ys) when imp = imp' ->
                    let hd1 =
                      let uu___149_6523 = hd1 in
                      let _0_447 =
                        FStar_Syntax_Subst.subst subst
                          hd1.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___149_6523.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___149_6523.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = _0_447
                      } in
                    let hd2 =
                      let uu___150_6525 = hd2 in
                      let _0_448 =
                        FStar_Syntax_Subst.subst subst
                          hd2.FStar_Syntax_Syntax.sort in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___150_6525.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___150_6525.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = _0_448
                      } in
                    let prob =
                      let _0_451 =
                        let _0_450 =
                          FStar_All.pipe_left invert_rel (p_rel orig) in
                        mk_problem scope orig hd1.FStar_Syntax_Syntax.sort
                          _0_450 hd2.FStar_Syntax_Syntax.sort None
                          "Formal parameter" in
                      FStar_All.pipe_left
                        (fun _0_449  -> FStar_TypeChecker_Common.TProb _0_449)
                        _0_451 in
                    let hd1 = FStar_Syntax_Syntax.freshen_bv hd1 in
                    let subst =
                      let _0_452 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd1))
                        :: _0_452 in
                    let env = FStar_TypeChecker_Env.push_bv env hd1 in
                    let uu____6535 =
                      aux ((hd1, imp) :: scope) env subst xs ys in
                    (match uu____6535 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi =
                           let _0_454 =
                             FStar_All.pipe_right (p_guard prob) Prims.fst in
                           let _0_453 =
                             FStar_Syntax_Util.close_forall [(hd1, imp)] phi in
                           FStar_Syntax_Util.mk_conj _0_454 _0_453 in
                         ((let uu____6560 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____6560
                           then
                             let _0_456 =
                               FStar_Syntax_Print.term_to_string phi in
                             let _0_455 = FStar_Syntax_Print.bv_to_string hd1 in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               _0_456 _0_455
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi))
                     | fail -> fail)
                | uu____6575 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch" in
              let scope = p_scope orig in
              let uu____6581 = aux scope env [] bs1 bs2 in
              match uu____6581 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl = solve_prob orig (Some phi) [] wl in
                  solve env (attempt sub_probs wl)
and solve_t: FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let _0_457 = compress_tprob wl problem in solve_t' env _0_457 wl
and solve_t': FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer orig msg = giveup_or_defer env orig wl msg in
        let rigid_rigid_delta env orig wl head1 head2 t1 t2 =
          let uu____6629 = head_matches_delta env wl t1 t2 in
          match uu____6629 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____6646,uu____6647) ->
                   let may_relate head =
                     match head.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_name _
                       |FStar_Syntax_Syntax.Tm_match _ -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____6669 -> false in
                   if ((may_relate head1) || (may_relate head2)) && wl.smt_ok
                   then
                     let guard =
                       if
                         problem.FStar_TypeChecker_Common.relation =
                           FStar_TypeChecker_Common.EQ
                       then mk_eq2 env t1 t2
                       else
                         (let has_type_guard t1 t2 =
                            match problem.FStar_TypeChecker_Common.element
                            with
                            | Some t -> FStar_Syntax_Util.mk_has_type t1 t t2
                            | None  ->
                                let x = FStar_Syntax_Syntax.new_bv None t1 in
                                let _0_459 =
                                  let _0_458 =
                                    FStar_Syntax_Syntax.bv_to_name x in
                                  FStar_Syntax_Util.mk_has_type t1 _0_458 t2 in
                                FStar_Syntax_Util.mk_forall x _0_459 in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1) in
                     let _0_460 = solve_prob orig (Some guard) [] wl in
                     solve env _0_460
                   else giveup env "head mismatch" orig
               | (uu____6687,Some (t1,t2)) ->
                   solve_t env
                     (let uu___151_6695 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___151_6695.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t1;
                        FStar_TypeChecker_Common.relation =
                          (uu___151_6695.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t2;
                        FStar_TypeChecker_Common.element =
                          (uu___151_6695.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___151_6695.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___151_6695.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___151_6695.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___151_6695.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___151_6695.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____6696,None ) ->
                   ((let uu____6703 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____6703
                     then
                       let _0_464 = FStar_Syntax_Print.term_to_string t1 in
                       let _0_463 = FStar_Syntax_Print.tag_of_term t1 in
                       let _0_462 = FStar_Syntax_Print.term_to_string t2 in
                       let _0_461 = FStar_Syntax_Print.tag_of_term t2 in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" _0_464 _0_463
                         _0_462 _0_461
                     else ());
                    (let uu____6705 = FStar_Syntax_Util.head_and_args t1 in
                     match uu____6705 with
                     | (head1,args1) ->
                         let uu____6731 = FStar_Syntax_Util.head_and_args t2 in
                         (match uu____6731 with
                          | (head2,args2) ->
                              let nargs = FStar_List.length args1 in
                              if nargs <> (FStar_List.length args2)
                              then
                                let _0_469 =
                                  let _0_468 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let _0_467 = args_to_string args1 in
                                  let _0_466 =
                                    FStar_Syntax_Print.term_to_string head2 in
                                  let _0_465 = args_to_string args2 in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    _0_468 _0_467 _0_466 _0_465 in
                                giveup env _0_469 orig
                              else
                                (let uu____6772 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let _0_470 =
                                        FStar_Syntax_Util.eq_args args1 args2 in
                                      _0_470 = FStar_Syntax_Util.Equal) in
                                 if uu____6772
                                 then
                                   let uu____6775 =
                                     solve_maybe_uinsts env orig head1 head2
                                       wl in
                                   match uu____6775 with
                                   | USolved wl ->
                                       let _0_471 =
                                         solve_prob orig None [] wl in
                                       solve env _0_471
                                   | UFailed msg -> giveup env msg orig
                                   | UDeferred wl ->
                                       solve env
                                         (defer "universe constraints" orig
                                            wl)
                                 else
                                   (let uu____6780 =
                                      base_and_refinement env wl t1 in
                                    match uu____6780 with
                                    | (base1,refinement1) ->
                                        let uu____6806 =
                                          base_and_refinement env wl t2 in
                                        (match uu____6806 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____6860 =
                                                    solve_maybe_uinsts env
                                                      orig head1 head2 wl in
                                                  (match uu____6860 with
                                                   | UFailed msg ->
                                                       giveup env msg orig
                                                   | UDeferred wl ->
                                                       solve env
                                                         (defer
                                                            "universe constraints"
                                                            orig wl)
                                                   | USolved wl ->
                                                       let subprobs =
                                                         FStar_List.map2
                                                           (fun uu____6870 
                                                              ->
                                                              fun uu____6871 
                                                                ->
                                                                match 
                                                                  (uu____6870,
                                                                    uu____6871)
                                                                with
                                                                | ((a,uu____6881),
                                                                   (a',uu____6883))
                                                                    ->
                                                                    let _0_473
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a' None
                                                                    "index" in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_472 
                                                                    ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_472)
                                                                    _0_473)
                                                           args1 args2 in
                                                       let formula =
                                                         FStar_Syntax_Util.mk_conj_l
                                                           (FStar_List.map
                                                              (fun p  ->
                                                                 Prims.fst
                                                                   (p_guard p))
                                                              subprobs) in
                                                       let wl =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl in
                                                       solve env
                                                         (attempt subprobs wl))
                                              | uu____6893 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1) in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2) in
                                                  solve_t env
                                                    (let uu___152_6926 =
                                                       problem in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___152_6926.FStar_TypeChecker_Common.rank)
                                                     }) wl)))))))) in
        let imitate orig env wl p =
          let uu____6946 = p in
          match uu____6946 with
          | (((u,k),xs,c),ps,(h,uu____6957,qs)) ->
              let xs = sn_binders env xs in
              let r = FStar_TypeChecker_Env.get_range env in
              let uu____7006 = imitation_sub_probs orig env xs ps qs in
              (match uu____7006 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let _0_478 = h gs_xs in
                     let _0_477 =
                       let _0_476 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_474  -> FStar_Util.Inl _0_474) in
                       FStar_All.pipe_right _0_476
                         (fun _0_475  -> Some _0_475) in
                     FStar_Syntax_Util.abs xs _0_478 _0_477 in
                   ((let uu____7045 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____7045
                     then
                       let _0_485 =
                         FStar_Syntax_Print.binders_to_string ", " xs in
                       let _0_484 = FStar_Syntax_Print.comp_to_string c in
                       let _0_483 = FStar_Syntax_Print.term_to_string im in
                       let _0_482 = FStar_Syntax_Print.tag_of_term im in
                       let _0_481 =
                         let _0_479 =
                           FStar_List.map (prob_to_string env) sub_probs in
                         FStar_All.pipe_right _0_479
                           (FStar_String.concat ", ") in
                       let _0_480 =
                         FStar_TypeChecker_Normalize.term_to_string env
                           formula in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         _0_485 _0_484 _0_483 _0_482 _0_481 _0_480
                     else ());
                    (let wl =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl in
                     solve env (attempt sub_probs wl)))) in
        let imitate' orig env wl uu___123_7064 =
          match uu___123_7064 with
          | None  -> giveup env "unable to compute subterms" orig
          | Some p -> imitate orig env wl p in
        let project orig env wl i p =
          let uu____7093 = p in
          match uu____7093 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env in
              let uu____7151 = FStar_List.nth ps i in
              (match uu____7151 with
               | (pi,uu____7154) ->
                   let uu____7159 = FStar_List.nth xs i in
                   (match uu____7159 with
                    | (xi,uu____7166) ->
                        let rec gs k =
                          let uu____7175 = FStar_Syntax_Util.arrow_formals k in
                          match uu____7175 with
                          | (bs,k) ->
                              let rec aux subst bs =
                                match bs with
                                | [] -> ([], [])
                                | (a,uu____7227)::tl ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst
                                        a.FStar_Syntax_Syntax.sort in
                                    let uu____7235 = new_uvar r xs k_a in
                                    (match uu____7235 with
                                     | (gi_xs,gi) ->
                                         let gi_xs =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env gi_xs in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r in
                                         let subst =
                                           (FStar_Syntax_Syntax.NT (a, gi_xs))
                                           :: subst in
                                         let uu____7254 = aux subst tl in
                                         (match uu____7254 with
                                          | (gi_xs',gi_ps') ->
                                              let _0_489 =
                                                let _0_486 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs in
                                                _0_486 :: gi_xs' in
                                              let _0_488 =
                                                let _0_487 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps in
                                                _0_487 :: gi_ps' in
                                              (_0_489, _0_488))) in
                              aux [] bs in
                        let uu____7271 =
                          let _0_490 = matches pi in
                          FStar_All.pipe_left Prims.op_Negation _0_490 in
                        if uu____7271
                        then None
                        else
                          (let uu____7274 = gs xi.FStar_Syntax_Syntax.sort in
                           match uu____7274 with
                           | (g_xs,uu____7281) ->
                               let xi = FStar_Syntax_Syntax.bv_to_name xi in
                               let proj =
                                 let _0_495 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi g_xs)
                                     None r in
                                 let _0_494 =
                                   let _0_493 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_491  -> FStar_Util.Inl _0_491) in
                                   FStar_All.pipe_right _0_493
                                     (fun _0_492  -> Some _0_492) in
                                 FStar_Syntax_Util.abs xs _0_495 _0_494 in
                               let sub =
                                 let _0_500 =
                                   let _0_499 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r in
                                   let _0_498 =
                                     let _0_497 =
                                       FStar_List.map
                                         (fun uu____7334  ->
                                            match uu____7334 with
                                            | (uu____7339,uu____7340,y) -> y)
                                         qs in
                                     FStar_All.pipe_left h _0_497 in
                                   mk_problem (p_scope orig) orig _0_499
                                     (p_rel orig) _0_498 None "projection" in
                                 FStar_All.pipe_left
                                   (fun _0_496  ->
                                      FStar_TypeChecker_Common.TProb _0_496)
                                   _0_500 in
                               ((let uu____7345 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "Rel") in
                                 if uu____7345
                                 then
                                   let _0_502 =
                                     FStar_Syntax_Print.term_to_string proj in
                                   let _0_501 = prob_to_string env sub in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n" _0_502
                                     _0_501
                                 else ());
                                (let wl =
                                   let _0_503 =
                                     Some
                                       (FStar_All.pipe_left Prims.fst
                                          (p_guard sub)) in
                                   solve_prob orig _0_503 [TERM (u, proj)] wl in
                                 let _0_505 = solve env (attempt [sub] wl) in
                                 FStar_All.pipe_left
                                   (fun _0_504  -> Some _0_504) _0_505))))) in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl =
          let uu____7375 = lhs in
          match uu____7375 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____7398 = FStar_Syntax_Util.arrow_formals_comp k_uv in
                match uu____7398 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      Some
                        (let _0_506 = decompose env t2 in
                         (((uv, k_uv), xs, c), ps, _0_506))
                    else
                      (let k_uv =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv in
                       let rec elim k args =
                         let uu____7489 =
                           let _0_507 =
                             (FStar_Syntax_Subst.compress k).FStar_Syntax_Syntax.n in
                           (_0_507, args) in
                         match uu____7489 with
                         | (uu____7497,[]) ->
                             Some
                               (let _0_508 = FStar_Syntax_Syntax.mk_Total k in
                                ([], _0_508))
                         | (FStar_Syntax_Syntax.Tm_uvar _,_)
                           |(FStar_Syntax_Syntax.Tm_app _,_) ->
                             let uu____7515 =
                               FStar_Syntax_Util.head_and_args k in
                             (match uu____7515 with
                              | (uv,uv_args) ->
                                  let uu____7544 =
                                    (FStar_Syntax_Subst.compress uv).FStar_Syntax_Syntax.n in
                                  (match uu____7544 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____7549) ->
                                       let uu____7562 =
                                         pat_vars env [] uv_args in
                                       (match uu____7562 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____7576  ->
                                                      let _0_512 =
                                                        let _0_511 =
                                                          Prims.fst
                                                            (let _0_510 =
                                                               let _0_509 =
                                                                 FStar_Syntax_Util.type_u
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 _0_509
                                                                 Prims.fst in
                                                             new_uvar
                                                               k.FStar_Syntax_Syntax.pos
                                                               scope _0_510) in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          _0_511 in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        _0_512)) in
                                            let c =
                                              FStar_Syntax_Syntax.mk_Total
                                                (Prims.fst
                                                   (let _0_514 =
                                                      let _0_513 =
                                                        FStar_Syntax_Util.type_u
                                                          () in
                                                      FStar_All.pipe_right
                                                        _0_513 Prims.fst in
                                                    new_uvar
                                                      k.FStar_Syntax_Syntax.pos
                                                      scope _0_514)) in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs c in
                                            let uv_sol =
                                              let _0_517 =
                                                Some
                                                  (FStar_Util.Inl
                                                     (let _0_516 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          (let _0_515 =
                                                             FStar_Syntax_Util.type_u
                                                               () in
                                                           FStar_All.pipe_right
                                                             _0_515 Prims.fst) in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.lcomp_of_comp
                                                        _0_516)) in
                                              FStar_Syntax_Util.abs scope k'
                                                _0_517 in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs, c)))
                                   | uu____7606 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs,c),uu____7611)
                             ->
                             let n_args = FStar_List.length args in
                             let n_xs = FStar_List.length xs in
                             if n_xs = n_args
                             then
                               let _0_519 = FStar_Syntax_Subst.open_comp xs c in
                               FStar_All.pipe_right _0_519
                                 (fun _0_518  -> Some _0_518)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____7653 =
                                    FStar_Util.first_N n_xs args in
                                  match uu____7653 with
                                  | (args,rest) ->
                                      let uu____7669 =
                                        FStar_Syntax_Subst.open_comp xs c in
                                      (match uu____7669 with
                                       | (xs,c) ->
                                           let _0_520 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c) rest in
                                           FStar_Util.bind_opt _0_520
                                             (fun uu____7684  ->
                                                match uu____7684 with
                                                | (xs',c) ->
                                                    Some
                                                      ((FStar_List.append xs
                                                          xs'), c))))
                               else
                                 (let uu____7706 =
                                    FStar_Util.first_N n_args xs in
                                  match uu____7706 with
                                  | (xs,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c))) None
                                          k.FStar_Syntax_Syntax.pos in
                                      let _0_523 =
                                        let _0_521 =
                                          FStar_Syntax_Syntax.mk_Total t in
                                        FStar_Syntax_Subst.open_comp xs
                                          _0_521 in
                                      FStar_All.pipe_right _0_523
                                        (fun _0_522  -> Some _0_522))
                         | uu____7759 ->
                             failwith
                               (let _0_526 =
                                  FStar_Syntax_Print.uvar_to_string uv in
                                let _0_525 =
                                  FStar_Syntax_Print.term_to_string k in
                                let _0_524 =
                                  FStar_Syntax_Print.term_to_string k_uv in
                                FStar_Util.format3
                                  "Impossible: ill-typed application %s : %s\n\t%s"
                                  _0_526 _0_525 _0_524) in
                       let _0_528 = elim k_uv ps in
                       FStar_Util.bind_opt _0_528
                         (fun uu____7793  ->
                            match uu____7793 with
                            | (xs,c) ->
                                Some
                                  (let _0_527 = decompose env t2 in
                                   (((uv, k_uv), xs, c), ps, _0_527)))) in
              let rec imitate_or_project n stopt i =
                if (i >= n) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt in
                   let tx = FStar_Unionfind.new_transaction () in
                   if i = (- (Prims.parse_int "1"))
                   then
                     let uu____7879 = imitate orig env wl st in
                     match uu____7879 with
                     | Failed uu____7884 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____7890 = project orig env wl i st in
                      match uu____7890 with
                      | None |Some (Failed _) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol)) in
              let check_head fvs1 t2 =
                let uu____7908 = FStar_Syntax_Util.head_and_args t2 in
                match uu____7908 with
                | (hd,uu____7919) ->
                    (match hd.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow _
                       |FStar_Syntax_Syntax.Tm_constant _
                        |FStar_Syntax_Syntax.Tm_abs _ -> true
                     | uu____7937 ->
                         let fvs_hd = FStar_Syntax_Free.names hd in
                         let uu____7940 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1 in
                         if uu____7940
                         then true
                         else
                           ((let uu____7943 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____7943
                             then
                               let _0_529 = names_to_string fvs_hd in
                               FStar_Util.print1 "Free variables are %s"
                                 _0_529
                             else ());
                            false)) in
              let imitate_ok t2 =
                let fvs_hd =
                  let _0_531 =
                    let _0_530 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right _0_530 Prims.fst in
                  FStar_All.pipe_right _0_531 FStar_Syntax_Free.names in
                let uu____7972 = FStar_Util.set_is_empty fvs_hd in
                if uu____7972
                then - (Prims.parse_int "1")
                else Prims.parse_int "0" in
              (match maybe_pat_vars with
               | Some vars ->
                   let t1 = sn env t1 in
                   let t2 = sn env t2 in
                   let fvs1 = FStar_Syntax_Free.names t1 in
                   let fvs2 = FStar_Syntax_Free.names t2 in
                   let uu____7981 = occurs_check env wl (uv, k_uv) t2 in
                   (match uu____7981 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let _0_533 =
                            let _0_532 = FStar_Option.get msg in
                            Prims.strcat "occurs-check failed: " _0_532 in
                          giveup_or_defer orig _0_533
                        else
                          (let uu____7990 =
                             FStar_Util.set_is_subset_of fvs2 fvs1 in
                           if uu____7990
                           then
                             let uu____7991 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t2))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ) in
                             (if uu____7991
                              then
                                let _0_534 = subterms args_lhs in
                                imitate' orig env wl _0_534
                              else
                                ((let uu____7994 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____7994
                                  then
                                    let _0_537 =
                                      FStar_Syntax_Print.term_to_string t1 in
                                    let _0_536 = names_to_string fvs1 in
                                    let _0_535 = names_to_string fvs2 in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      _0_537 _0_536 _0_535
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t2
                                    | uu____7999 ->
                                        let _0_538 = sn_binders env vars in
                                        u_abs k_uv _0_538 t2 in
                                  let wl =
                                    solve_prob orig None
                                      [TERM ((uv, k_uv), sol)] wl in
                                  solve env wl)))
                           else
                             if
                               ((Prims.op_Negation patterns_only) &&
                                  wl.defer_ok)
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                             then
                               solve env
                                 (defer
                                    "flex pattern/rigid: occurs or freevar check"
                                    orig wl)
                             else
                               (let uu____8005 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t2) in
                                if uu____8005
                                then
                                  ((let uu____8007 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel") in
                                    if uu____8007
                                    then
                                      let _0_541 =
                                        FStar_Syntax_Print.term_to_string t1 in
                                      let _0_540 = names_to_string fvs1 in
                                      let _0_539 = names_to_string fvs2 in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        _0_541 _0_540 _0_539
                                    else ());
                                   (let _0_542 = subterms args_lhs in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) _0_542
                                      (- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | None  when patterns_only -> giveup env "not a pattern" orig
               | None  ->
                   if wl.defer_ok
                   then solve env (defer "not a pattern" orig wl)
                   else
                     (let uu____8018 =
                        let _0_543 = FStar_Syntax_Free.names t1 in
                        check_head _0_543 t2 in
                      if uu____8018
                      then
                        let im_ok = imitate_ok t2 in
                        ((let uu____8021 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel") in
                          if uu____8021
                          then
                            let _0_544 = FStar_Syntax_Print.term_to_string t1 in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              _0_544
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let _0_545 = subterms args_lhs in
                          imitate_or_project (FStar_List.length args_lhs)
                            _0_545 im_ok))
                      else giveup env "head-symbol is free" orig)) in
        let flex_flex orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____8064 =
               match uu____8064 with
               | (t,u,k,args) ->
                   let uu____8094 = FStar_Syntax_Util.arrow_formals k in
                   (match uu____8094 with
                    | (all_formals,uu____8105) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args =
                          match (formals, args) with
                          | ([],[]) ->
                              let pat_args =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____8197  ->
                                        match uu____8197 with
                                        | (x,imp) ->
                                            let _0_546 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x in
                                            (_0_546, imp))) in
                              let pattern_vars = FStar_List.rev pattern_vars in
                              let kk =
                                let uu____8211 = FStar_Syntax_Util.type_u () in
                                match uu____8211 with
                                | (t,uu____8215) ->
                                    Prims.fst
                                      (new_uvar t.FStar_Syntax_Syntax.pos
                                         pattern_vars t) in
                              let uu____8216 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars kk in
                              (match uu____8216 with
                               | (t',tm_u1) ->
                                   let uu____8223 = destruct_flex_t t' in
                                   (match uu____8223 with
                                    | (uu____8243,u1,k1,uu____8246) ->
                                        let sol =
                                          TERM
                                            (let _0_547 =
                                               u_abs k all_formals t' in
                                             ((u, k), _0_547)) in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args) None
                                            t.FStar_Syntax_Syntax.pos in
                                        (sol, (t_app, u1, k1, pat_args))))
                          | (formal::formals,hd::tl) ->
                              let uu____8333 = pat_var_opt env pat_args hd in
                              (match uu____8333 with
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
                                              (fun uu____8362  ->
                                                 match uu____8362 with
                                                 | (x,uu____8366) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (Prims.fst y))) in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals tl
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (Prims.fst y).FStar_Syntax_Syntax.sort in
                                      let uu____8372 =
                                        Prims.op_Negation
                                          (FStar_Util.set_is_subset_of fvs
                                             pattern_var_set) in
                                      if uu____8372
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals tl
                                      else
                                        (let _0_548 =
                                           FStar_Util.set_add
                                             (Prims.fst formal)
                                             pattern_var_set in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) _0_548 formals tl)))
                          | uu____8380 -> failwith "Impossible" in
                        let _0_549 = FStar_Syntax_Syntax.new_bv_set () in
                        aux [] [] _0_549 all_formals args) in
             let solve_both_pats wl uu____8437 uu____8438 r =
               match (uu____8437, uu____8438) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____8592 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys) in
                   if uu____8592
                   then
                     let _0_550 = solve_prob orig None [] wl in
                     solve env _0_550
                   else
                     (let xs = sn_binders env xs in
                      let ys = sn_binders env ys in
                      let zs = intersect_vars xs ys in
                      (let uu____8610 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel") in
                       if uu____8610
                       then
                         let _0_555 =
                           FStar_Syntax_Print.binders_to_string ", " xs in
                         let _0_554 =
                           FStar_Syntax_Print.binders_to_string ", " ys in
                         let _0_553 =
                           FStar_Syntax_Print.binders_to_string ", " zs in
                         let _0_552 = FStar_Syntax_Print.term_to_string k1 in
                         let _0_551 = FStar_Syntax_Print.term_to_string k2 in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           _0_555 _0_554 _0_553 _0_552 _0_551
                       else ());
                      (let subst_k k xs args =
                         let xs_len = FStar_List.length xs in
                         let args_len = FStar_List.length args in
                         if xs_len = args_len
                         then
                           let _0_556 =
                             FStar_Syntax_Util.subst_of_list xs args in
                           FStar_Syntax_Subst.subst _0_556 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____8658 = FStar_Util.first_N args_len xs in
                              match uu____8658 with
                              | (xs,xs_rest) ->
                                  let k =
                                    let _0_557 =
                                      FStar_Syntax_Syntax.mk_GTotal k in
                                    FStar_Syntax_Util.arrow xs_rest _0_557 in
                                  let _0_558 =
                                    FStar_Syntax_Util.subst_of_list xs args in
                                  FStar_Syntax_Subst.subst _0_558 k)
                           else
                             failwith
                               (let _0_561 =
                                  FStar_Syntax_Print.term_to_string k in
                                let _0_560 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs in
                                let _0_559 =
                                  FStar_Syntax_Print.args_to_string args in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  _0_561 _0_560 _0_559) in
                       let uu____8689 =
                         let uu____8695 =
                           FStar_Syntax_Util.arrow_formals
                             (FStar_TypeChecker_Normalize.normalize
                                [FStar_TypeChecker_Normalize.Beta] env k1) in
                         match uu____8695 with
                         | (bs,k1') ->
                             let uu____8720 =
                               FStar_Syntax_Util.arrow_formals
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env k2) in
                             (match uu____8720 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1 in
                                  let k2'_ys = subst_k k2' cs args2 in
                                  let sub_prob =
                                    let _0_563 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding" in
                                    FStar_All.pipe_left
                                      (fun _0_562  ->
                                         FStar_TypeChecker_Common.TProb
                                           _0_562) _0_563 in
                                  let uu____8750 =
                                    let _0_565 =
                                      (FStar_Syntax_Subst.compress k1').FStar_Syntax_Syntax.n in
                                    let _0_564 =
                                      (FStar_Syntax_Subst.compress k2').FStar_Syntax_Syntax.n in
                                    (_0_565, _0_564) in
                                  (match uu____8750 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____8758,uu____8759) ->
                                       (k1', [sub_prob])
                                   | (uu____8763,FStar_Syntax_Syntax.Tm_type
                                      uu____8764) -> (k2', [sub_prob])
                                   | uu____8768 ->
                                       let uu____8771 =
                                         FStar_Syntax_Util.type_u () in
                                       (match uu____8771 with
                                        | (t,uu____8780) ->
                                            let uu____8781 = new_uvar r zs t in
                                            (match uu____8781 with
                                             | (k_zs,uu____8790) ->
                                                 let kprob =
                                                   let _0_567 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding" in
                                                   FStar_All.pipe_left
                                                     (fun _0_566  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_566) _0_567 in
                                                 (k_zs, [sub_prob; kprob]))))) in
                       match uu____8689 with
                       | (k_u',sub_probs) ->
                           let uu____8803 =
                             let _0_573 =
                               let _0_568 = new_uvar r zs k_u' in
                               FStar_All.pipe_left Prims.fst _0_568 in
                             let _0_572 =
                               let _0_569 = FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow xs _0_569 in
                             let _0_571 =
                               let _0_570 = FStar_Syntax_Syntax.mk_Total k_u' in
                               FStar_Syntax_Util.arrow ys _0_570 in
                             (_0_573, _0_572, _0_571) in
                           (match uu____8803 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs u_zs in
                                let uu____8829 =
                                  occurs_check env wl (u1, k1) sub1 in
                                (match uu____8829 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1) in
                                        let uu____8853 =
                                          FStar_Unionfind.equivalent u1 u2 in
                                        if uu____8853
                                        then
                                          let wl =
                                            solve_prob orig None [sol1] wl in
                                          solve env wl
                                        else
                                          (let sub2 = u_abs knew2 ys u_zs in
                                           let uu____8860 =
                                             occurs_check env wl (u2, k2)
                                               sub2 in
                                           match uu____8860 with
                                           | (occurs_ok,msg) ->
                                               if Prims.op_Negation occurs_ok
                                               then
                                                 giveup_or_defer orig
                                                   "flex-flex: failed occurs check"
                                               else
                                                 (let sol2 =
                                                    TERM ((u2, k2), sub2) in
                                                  let wl =
                                                    solve_prob orig None
                                                      [sol1; sol2] wl in
                                                  solve env
                                                    (attempt sub_probs wl)))))))) in
             let solve_one_pat uu____8912 uu____8913 =
               match (uu____8912, uu____8913) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____9017 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel") in
                     if uu____9017
                     then
                       let _0_575 = FStar_Syntax_Print.term_to_string t1 in
                       let _0_574 = FStar_Syntax_Print.term_to_string t2 in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n" _0_575
                         _0_574
                     else ());
                    (let uu____9019 = FStar_Unionfind.equivalent u1 u2 in
                     if uu____9019
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____9029  ->
                              fun uu____9030  ->
                                match (uu____9029, uu____9030) with
                                | ((a,uu____9040),(t2,uu____9042)) ->
                                    let _0_578 =
                                      let _0_576 =
                                        FStar_Syntax_Syntax.bv_to_name a in
                                      mk_problem (p_scope orig) orig _0_576
                                        FStar_TypeChecker_Common.EQ t2 None
                                        "flex-flex index" in
                                    FStar_All.pipe_right _0_578
                                      (fun _0_577  ->
                                         FStar_TypeChecker_Common.TProb
                                           _0_577)) xs args2 in
                       let guard =
                         FStar_Syntax_Util.mk_conj_l
                           (FStar_List.map
                              (fun p  ->
                                 FStar_All.pipe_right (p_guard p) Prims.fst)
                              sub_probs) in
                       let wl = solve_prob orig (Some guard) [] wl in
                       solve env (attempt sub_probs wl)
                     else
                       (let t2 = sn env t2 in
                        let rhs_vars = FStar_Syntax_Free.names t2 in
                        let uu____9058 = occurs_check env wl (u1, k1) t2 in
                        match uu____9058 with
                        | (occurs_ok,uu____9067) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs in
                            let uu____9072 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars) in
                            if uu____9072
                            then
                              let sol =
                                TERM
                                  (let _0_579 = u_abs k1 xs t2 in
                                   ((u1, k1), _0_579)) in
                              let wl = solve_prob orig None [sol] wl in
                              solve env wl
                            else
                              (let uu____9086 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok) in
                               if uu____9086
                               then
                                 let uu____9087 =
                                   force_quasi_pattern (Some xs)
                                     (t2, u2, k2, args2) in
                                 match uu____9087 with
                                 | (sol,(uu____9101,u2,k2,ys)) ->
                                     let wl =
                                       extend_solution (p_pid orig) [sol] wl in
                                     ((let uu____9111 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern") in
                                       if uu____9111
                                       then
                                         let _0_580 = uvi_to_string env sol in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           _0_580
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl
                                       | uu____9116 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer orig "flex-flex constraint")))) in
             let uu____9118 = lhs in
             match uu____9118 with
             | (t1,u1,k1,args1) ->
                 let uu____9123 = rhs in
                 (match uu____9123 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1 in
                      let maybe_pat_vars2 = pat_vars env [] args2 in
                      let r = t2.FStar_Syntax_Syntax.pos in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (Some xs,Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (Some xs,None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (None ,Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____9149 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____9155 =
                                force_quasi_pattern None (t1, u1, k1, args1) in
                              match uu____9155 with
                              | (sol,uu____9162) ->
                                  let wl =
                                    extend_solution (p_pid orig) [sol] wl in
                                  ((let uu____9165 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern") in
                                    if uu____9165
                                    then
                                      let _0_581 = uvi_to_string env sol in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        _0_581
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl
                                    | uu____9170 ->
                                        giveup env "impossible" orig)))))) in
        let orig = FStar_TypeChecker_Common.TProb problem in
        let uu____9172 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs in
        if uu____9172
        then let _0_582 = solve_prob orig None [] wl in solve env _0_582
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs in
           let t2 = problem.FStar_TypeChecker_Common.rhs in
           let uu____9176 = FStar_Util.physical_equality t1 t2 in
           if uu____9176
           then let _0_583 = solve_prob orig None [] wl in solve env _0_583
           else
             ((let uu____9179 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck") in
               if uu____9179
               then
                 let _0_584 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid in
                 FStar_Util.print1 "Attempting %s\n" _0_584
               else ());
              (let r = FStar_TypeChecker_Env.get_range env in
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
                   let mk_c c uu___124_9225 =
                     match uu___124_9225 with
                     | [] -> c
                     | bs ->
                         FStar_Syntax_Syntax.mk_Total
                           ((FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_arrow (bs, c))) None
                              c.FStar_Syntax_Syntax.pos) in
                   let uu____9260 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                   (match uu____9260 with
                    | ((bs1,c1),(bs2,c2)) ->
                        solve_binders env bs1 bs2 orig wl
                          (fun scope  ->
                             fun env  ->
                               fun subst  ->
                                 let c1 =
                                   FStar_Syntax_Subst.subst_comp subst c1 in
                                 let c2 =
                                   FStar_Syntax_Subst.subst_comp subst c2 in
                                 let rel =
                                   let uu____9346 =
                                     FStar_Options.use_eq_at_higher_order () in
                                   if uu____9346
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation in
                                 let _0_586 =
                                   mk_problem scope orig c1 rel c2 None
                                     "function co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_585  ->
                                      FStar_TypeChecker_Common.CProb _0_585)
                                   _0_586))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___125_9422 =
                     match uu___125_9422 with
                     | [] -> t
                     | bs ->
                         (FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs (bs, t, l))) None
                           t.FStar_Syntax_Syntax.pos in
                   let uu____9461 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2)) in
                   (match uu____9461 with
                    | ((bs1,tbody1),(bs2,tbody2)) ->
                        solve_binders env bs1 bs2 orig wl
                          (fun scope  ->
                             fun env  ->
                               fun subst  ->
                                 let _0_590 =
                                   let _0_589 =
                                     FStar_Syntax_Subst.subst subst tbody1 in
                                   let _0_588 =
                                     FStar_Syntax_Subst.subst subst tbody2 in
                                   mk_problem scope orig _0_589
                                     problem.FStar_TypeChecker_Common.relation
                                     _0_588 None "lambda co-domain" in
                                 FStar_All.pipe_left
                                   (fun _0_587  ->
                                      FStar_TypeChecker_Common.TProb _0_587)
                                   _0_590))
               | (FStar_Syntax_Syntax.Tm_abs _,_)
                 |(_,FStar_Syntax_Syntax.Tm_abs _) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____9558 -> true
                     | uu____9573 -> false in
                   let maybe_eta t =
                     if is_abs t
                     then FStar_Util.Inl t
                     else
                       (let t =
                          FStar_TypeChecker_Normalize.eta_expand wl.tcenv t in
                        if is_abs t
                        then FStar_Util.Inl t
                        else FStar_Util.Inr t) in
                   let uu____9601 =
                     let _0_592 = maybe_eta t1 in
                     let _0_591 = maybe_eta t2 in (_0_592, _0_591) in
                   (match uu____9601 with
                    | (FStar_Util.Inl t1,FStar_Util.Inl t2) ->
                        solve_t env
                          (let uu___153_9638 = problem in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___153_9638.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t1;
                             FStar_TypeChecker_Common.relation =
                               (uu___153_9638.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t2;
                             FStar_TypeChecker_Common.element =
                               (uu___153_9638.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___153_9638.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___153_9638.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___153_9638.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___153_9638.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___153_9638.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs)
                      |(FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____9671 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                        if uu____9671
                        then
                          let _0_593 = destruct_flex_pattern env not_abs in
                          solve_t_flex_rigid true orig _0_593 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____9673 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____9684,FStar_Syntax_Syntax.Tm_refine uu____9685) ->
                   let uu____9694 = as_refinement env wl t1 in
                   (match uu____9694 with
                    | (x1,phi1) ->
                        let uu____9699 = as_refinement env wl t2 in
                        (match uu____9699 with
                         | (x2,phi2) ->
                             let base_prob =
                               let _0_595 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type" in
                               FStar_All.pipe_left
                                 (fun _0_594  ->
                                    FStar_TypeChecker_Common.TProb _0_594)
                                 _0_595 in
                             let x1 = FStar_Syntax_Syntax.freshen_bv x1 in
                             let subst =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)] in
                             let phi1 = FStar_Syntax_Subst.subst subst phi1 in
                             let phi2 = FStar_Syntax_Subst.subst subst phi2 in
                             let env = FStar_TypeChecker_Env.push_bv env x1 in
                             let mk_imp imp phi1 phi2 =
                               let _0_596 = imp phi1 phi2 in
                               FStar_All.pipe_right _0_596
                                 (guard_on_element problem x1) in
                             let fallback uu____9738 =
                               let impl =
                                 if
                                   problem.FStar_TypeChecker_Common.relation
                                     = FStar_TypeChecker_Common.EQ
                                 then
                                   mk_imp FStar_Syntax_Util.mk_iff phi1 phi2
                                 else
                                   mk_imp FStar_Syntax_Util.mk_imp phi1 phi2 in
                               let guard =
                                 let _0_597 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     Prims.fst in
                                 FStar_Syntax_Util.mk_conj _0_597 impl in
                               let wl = solve_prob orig (Some guard) [] wl in
                               solve env (attempt [base_prob] wl) in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let _0_601 =
                                   let _0_600 =
                                     let _0_599 =
                                       FStar_Syntax_Syntax.mk_binder x1 in
                                     _0_599 :: (p_scope orig) in
                                   mk_problem _0_600 orig phi1
                                     FStar_TypeChecker_Common.EQ phi2 None
                                     "refinement formula" in
                                 FStar_All.pipe_left
                                   (fun _0_598  ->
                                      FStar_TypeChecker_Common.TProb _0_598)
                                   _0_601 in
                               let uu____9752 =
                                 solve env
                                   (let uu___154_9753 = wl in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___154_9753.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___154_9753.smt_ok);
                                      tcenv = (uu___154_9753.tcenv)
                                    }) in
                               (match uu____9752 with
                                | Failed uu____9757 -> fallback ()
                                | Success uu____9760 ->
                                    let guard =
                                      let _0_604 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob) Prims.fst in
                                      let _0_603 =
                                        let _0_602 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob) Prims.fst in
                                        FStar_All.pipe_right _0_602
                                          (guard_on_element problem x1) in
                                      FStar_Syntax_Util.mk_conj _0_604 _0_603 in
                                    let wl =
                                      solve_prob orig (Some guard) [] wl in
                                    let wl =
                                      let uu___155_9772 = wl in
                                      {
                                        attempting =
                                          (uu___155_9772.attempting);
                                        wl_deferred =
                                          (uu___155_9772.wl_deferred);
                                        ctr =
                                          (wl.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___155_9772.defer_ok);
                                        smt_ok = (uu___155_9772.smt_ok);
                                        tcenv = (uu___155_9772.tcenv)
                                      } in
                                    solve env (attempt [base_prob] wl))
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
                   let _0_606 = destruct_flex_t t1 in
                   let _0_605 = destruct_flex_t t2 in
                   flex_flex orig _0_606 _0_605
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
                   let _0_607 = destruct_flex_pattern env t1 in
                   solve_t_flex_rigid false orig _0_607 t2 wl
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
                     (let uu___156_9886 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___156_9886.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___156_9886.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___156_9886.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___156_9886.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___156_9886.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___156_9886.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___156_9886.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___156_9886.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___156_9886.FStar_TypeChecker_Common.rank)
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
                     (let new_rel = problem.FStar_TypeChecker_Common.relation in
                      let uu____9904 =
                        let _0_608 = is_top_level_prob orig in
                        FStar_All.pipe_left Prims.op_Negation _0_608 in
                      if uu____9904
                      then
                        let _0_611 =
                          FStar_All.pipe_left
                            (fun _0_609  ->
                               FStar_TypeChecker_Common.TProb _0_609)
                            (let uu___157_9907 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___157_9907.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___157_9907.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___157_9907.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___157_9907.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___157_9907.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___157_9907.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___157_9907.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___157_9907.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___157_9907.FStar_TypeChecker_Common.rank)
                             }) in
                        let _0_610 = destruct_flex_pattern env t1 in
                        solve_t_flex_rigid false _0_611 _0_610 t2 wl
                      else
                        (let uu____9909 = base_and_refinement env wl t2 in
                         match uu____9909 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let _0_614 =
                                    FStar_All.pipe_left
                                      (fun _0_612  ->
                                         FStar_TypeChecker_Common.TProb
                                           _0_612)
                                      (let uu___158_9941 = problem in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___158_9941.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___158_9941.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___158_9941.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___158_9941.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___158_9941.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___158_9941.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___158_9941.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___158_9941.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___158_9941.FStar_TypeChecker_Common.rank)
                                       }) in
                                  let _0_613 = destruct_flex_pattern env t1 in
                                  solve_t_flex_rigid false _0_614 _0_613
                                    t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___159_9953 = y in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___159_9953.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___159_9953.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    } in
                                  let impl = guard_on_element problem y' phi in
                                  let base_prob =
                                    let _0_616 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type" in
                                    FStar_All.pipe_left
                                      (fun _0_615  ->
                                         FStar_TypeChecker_Common.TProb
                                           _0_615) _0_616 in
                                  let guard =
                                    let _0_617 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob) Prims.fst in
                                    FStar_Syntax_Util.mk_conj _0_617 impl in
                                  let wl = solve_prob orig (Some guard) [] wl in
                                  solve env (attempt [base_prob] wl))))
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
                     (let uu____9982 = base_and_refinement env wl t1 in
                      match uu____9982 with
                      | (t_base,uu____9993) ->
                          solve_t env
                            (let uu___160_10008 = problem in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___160_10008.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___160_10008.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___160_10008.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___160_10008.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___160_10008.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___160_10008.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___160_10008.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___160_10008.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____10011,uu____10012) ->
                   let t2 =
                     let _0_618 = base_and_refinement env wl t2 in
                     FStar_All.pipe_left force_refinement _0_618 in
                   solve_t env
                     (let uu___161_10027 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___161_10027.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___161_10027.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___161_10027.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t2;
                        FStar_TypeChecker_Common.element =
                          (uu___161_10027.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___161_10027.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___161_10027.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___161_10027.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___161_10027.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___161_10027.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____10028,FStar_Syntax_Syntax.Tm_refine uu____10029) ->
                   let t1 =
                     let _0_619 = base_and_refinement env wl t1 in
                     FStar_All.pipe_left force_refinement _0_619 in
                   solve_t env
                     (let uu___162_10044 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_10044.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t1;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_10044.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___162_10044.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___162_10044.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_10044.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_10044.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_10044.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_10044.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_10044.FStar_TypeChecker_Common.rank)
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
                     let _0_620 = FStar_Syntax_Util.head_and_args t1 in
                     FStar_All.pipe_right _0_620 Prims.fst in
                   let head2 =
                     let _0_621 = FStar_Syntax_Util.head_and_args t2 in
                     FStar_All.pipe_right _0_621 Prims.fst in
                   let uu____10113 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ) in
                   if uu____10113
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1 in
                     let uv2 = FStar_Syntax_Free.uvars t2 in
                     let uu____10122 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2) in
                     (if uu____10122
                      then
                        let guard =
                          let uu____10129 =
                            let _0_622 = FStar_Syntax_Util.eq_tm t1 t2 in
                            _0_622 = FStar_Syntax_Util.Equal in
                          if uu____10129
                          then None
                          else
                            (let _0_624 = mk_eq2 env t1 t2 in
                             FStar_All.pipe_left (fun _0_623  -> Some _0_623)
                               _0_624) in
                        let _0_625 = solve_prob orig guard [] wl in
                        solve env _0_625
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t1,uu____10136,uu____10137),uu____10138) ->
                   solve_t' env
                     (let uu___163_10157 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___163_10157.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t1;
                        FStar_TypeChecker_Common.relation =
                          (uu___163_10157.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___163_10157.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___163_10157.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___163_10157.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___163_10157.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___163_10157.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___163_10157.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___163_10157.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____10160,FStar_Syntax_Syntax.Tm_ascribed
                  (t2,uu____10162,uu____10163)) ->
                   solve_t' env
                     (let uu___164_10182 = problem in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_10182.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___164_10182.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___164_10182.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t2;
                        FStar_TypeChecker_Common.element =
                          (uu___164_10182.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_10182.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_10182.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_10182.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_10182.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_10182.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let _,_)
                 |(FStar_Syntax_Syntax.Tm_meta _,_)
                  |(FStar_Syntax_Syntax.Tm_delayed _,_)
                   |(_,FStar_Syntax_Syntax.Tm_meta _)
                    |(_,FStar_Syntax_Syntax.Tm_delayed _)
                     |(_,FStar_Syntax_Syntax.Tm_let _)
                   ->
                   failwith
                     (let _0_627 = FStar_Syntax_Print.tag_of_term t1 in
                      let _0_626 = FStar_Syntax_Print.tag_of_term t2 in
                      FStar_Util.format2 "Impossible: %s and %s" _0_627
                        _0_626)
               | uu____10195 -> giveup env "head tag mismatch" orig)))
and solve_c:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem ->
      worklist -> solution
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs in
        let c2 = problem.FStar_TypeChecker_Common.rhs in
        let orig = FStar_TypeChecker_Common.CProb problem in
        let sub_prob t1 rel t2 reason =
          mk_problem (p_scope orig) orig t1 rel t2 None reason in
        let solve_eq c1_comp c2_comp =
          (let uu____10227 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____10227
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____10235  ->
                  fun uu____10236  ->
                    match (uu____10235, uu____10236) with
                    | ((a1,uu____10246),(a2,uu____10248)) ->
                        let _0_629 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg" in
                        FStar_All.pipe_left
                          (fun _0_628  ->
                             FStar_TypeChecker_Common.TProb _0_628) _0_629)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args in
           let guard =
             FStar_Syntax_Util.mk_conj_l
               (FStar_List.map
                  (fun p  -> FStar_All.pipe_right (p_guard p) Prims.fst)
                  sub_probs) in
           let wl = solve_prob orig (Some guard) [] wl in
           solve env (attempt sub_probs wl)) in
        let solve_sub c1 edge c2 =
          let r = FStar_TypeChecker_Env.get_range env in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then
            let wp =
              match c1.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____10277)::[] -> wp1
              | uu____10290 ->
                  failwith
                    (let _0_630 =
                       FStar_Range.string_of_range
                         (FStar_Ident.range_of_lid
                            c1.FStar_Syntax_Syntax.effect_name) in
                     FStar_Util.format1
                       "Unexpected number of indices on a normalized effect (%s)"
                       _0_630) in
            let c1 =
              let _0_632 =
                let _0_631 =
                  FStar_Syntax_Syntax.as_arg
                    (edge.FStar_TypeChecker_Env.mlift
                       c1.FStar_Syntax_Syntax.result_typ wp) in
                [_0_631] in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (c1.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (c2.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (c1.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args = _0_632;
                FStar_Syntax_Syntax.flags = (c1.FStar_Syntax_Syntax.flags)
              } in
            solve_eq c1 c2
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___126_10302  ->
                       match uu___126_10302 with
                       | FStar_Syntax_Syntax.TOTAL 
                         |FStar_Syntax_Syntax.MLEFFECT 
                          |FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____10303 -> false)) in
             let uu____10304 =
               match ((c1.FStar_Syntax_Syntax.effect_args),
                       (c2.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____10328)::uu____10329,(wp2,uu____10331)::uu____10332)
                   -> (wp1, wp2)
               | uu____10373 ->
                   failwith
                     (let _0_634 =
                        FStar_Syntax_Print.lid_to_string
                          c1.FStar_Syntax_Syntax.effect_name in
                      let _0_633 =
                        FStar_Syntax_Print.lid_to_string
                          c2.FStar_Syntax_Syntax.effect_name in
                      FStar_Util.format2
                        "Got effects %s and %s, expected normalized effects"
                        _0_634 _0_633) in
             match uu____10304 with
             | (wpc1,wpc2) ->
                 let uu____10402 = FStar_Util.physical_equality wpc1 wpc2 in
                 if uu____10402
                 then
                   let _0_635 =
                     problem_using_guard orig
                       c1.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c2.FStar_Syntax_Syntax.result_typ None "result type" in
                   solve_t env _0_635 wl
                 else
                   (let c2_decl =
                      FStar_TypeChecker_Env.get_effect_decl env
                        c2.FStar_Syntax_Syntax.effect_name in
                    let g =
                      if env.FStar_TypeChecker_Env.lax
                      then FStar_Syntax_Util.t_true
                      else
                        if is_null_wp_2
                        then
                          ((let uu____10412 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____10412
                            then
                              FStar_Util.print_string
                                "Using trivial wp ... \n"
                            else ());
                           (FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_app
                                 (let _0_643 =
                                    let _0_637 =
                                      let _0_636 =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env
                                          c1.FStar_Syntax_Syntax.result_typ in
                                      [_0_636] in
                                    FStar_TypeChecker_Env.inst_effect_fun_with
                                      _0_637 env c2_decl
                                      c2_decl.FStar_Syntax_Syntax.trivial in
                                  let _0_642 =
                                    let _0_641 =
                                      FStar_Syntax_Syntax.as_arg
                                        c1.FStar_Syntax_Syntax.result_typ in
                                    let _0_640 =
                                      let _0_639 =
                                        let _0_638 =
                                          edge.FStar_TypeChecker_Env.mlift
                                            c1.FStar_Syntax_Syntax.result_typ
                                            wpc1 in
                                        FStar_All.pipe_left
                                          FStar_Syntax_Syntax.as_arg _0_638 in
                                      [_0_639] in
                                    _0_641 :: _0_640 in
                                  (_0_643, _0_642))))
                             (Some
                                (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                             r)
                        else
                          (FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_app
                                (let _0_653 =
                                   let _0_645 =
                                     let _0_644 =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c2.FStar_Syntax_Syntax.result_typ in
                                     [_0_644] in
                                   FStar_TypeChecker_Env.inst_effect_fun_with
                                     _0_645 env c2_decl
                                     c2_decl.FStar_Syntax_Syntax.stronger in
                                 let _0_652 =
                                   let _0_651 =
                                     FStar_Syntax_Syntax.as_arg
                                       c2.FStar_Syntax_Syntax.result_typ in
                                   let _0_650 =
                                     let _0_649 =
                                       FStar_Syntax_Syntax.as_arg wpc2 in
                                     let _0_648 =
                                       let _0_647 =
                                         let _0_646 =
                                           edge.FStar_TypeChecker_Env.mlift
                                             c1.FStar_Syntax_Syntax.result_typ
                                             wpc1 in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg _0_646 in
                                       [_0_647] in
                                     _0_649 :: _0_648 in
                                   _0_651 :: _0_650 in
                                 (_0_653, _0_652))))
                            (Some
                               (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                            r in
                    let base_prob =
                      let _0_655 =
                        sub_prob c1.FStar_Syntax_Syntax.result_typ
                          problem.FStar_TypeChecker_Common.relation
                          c2.FStar_Syntax_Syntax.result_typ "result type" in
                      FStar_All.pipe_left
                        (fun _0_654  -> FStar_TypeChecker_Common.TProb _0_654)
                        _0_655 in
                    let wl =
                      let _0_659 =
                        let _0_658 =
                          let _0_657 =
                            FStar_All.pipe_right (p_guard base_prob)
                              Prims.fst in
                          FStar_Syntax_Util.mk_conj _0_657 g in
                        FStar_All.pipe_left (fun _0_656  -> Some _0_656)
                          _0_658 in
                      solve_prob orig _0_659 [] wl in
                    solve env (attempt [base_prob] wl))) in
        let uu____10446 = FStar_Util.physical_equality c1 c2 in
        if uu____10446
        then let _0_660 = solve_prob orig None [] wl in solve env _0_660
        else
          ((let uu____10449 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____10449
            then
              let _0_662 = FStar_Syntax_Print.comp_to_string c1 in
              let _0_661 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" _0_662
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                _0_661
            else ());
           (let uu____10451 =
              let _0_664 = FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let _0_663 = FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (_0_664, _0_663) in
            match uu____10451 with
            | (c1,c2) ->
                (match ((c1.FStar_Syntax_Syntax.n),
                         (c2.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____10457),FStar_Syntax_Syntax.Total
                    (t2,uu____10459)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let _0_665 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env _0_665 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____10474,FStar_Syntax_Syntax.Total uu____10475) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,_),FStar_Syntax_Syntax.Total (t2,_))
                   |(FStar_Syntax_Syntax.GTotal
                     (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                    |(FStar_Syntax_Syntax.Total
                      (t1,_),FStar_Syntax_Syntax.GTotal (t2,_))
                     ->
                     let _0_666 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type" in
                     solve_t env _0_666 wl
                 | (FStar_Syntax_Syntax.GTotal _,FStar_Syntax_Syntax.Comp _)
                   |(FStar_Syntax_Syntax.Total _,FStar_Syntax_Syntax.Comp _)
                     ->
                     let _0_669 =
                       let uu___165_10530 = problem in
                       let _0_668 =
                         let _0_667 =
                           FStar_TypeChecker_Normalize.comp_to_comp_typ env
                             c1 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           _0_667 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___165_10530.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = _0_668;
                         FStar_TypeChecker_Common.relation =
                           (uu___165_10530.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___165_10530.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___165_10530.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___165_10530.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___165_10530.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___165_10530.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___165_10530.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___165_10530.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env _0_669 wl
                 | (FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.GTotal _)
                   |(FStar_Syntax_Syntax.Comp _,FStar_Syntax_Syntax.Total _)
                     ->
                     let _0_672 =
                       let uu___166_10537 = problem in
                       let _0_671 =
                         let _0_670 =
                           FStar_TypeChecker_Normalize.comp_to_comp_typ env
                             c2 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           _0_670 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___166_10537.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___166_10537.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___166_10537.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = _0_671;
                         FStar_TypeChecker_Common.element =
                           (uu___166_10537.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___166_10537.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___166_10537.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___166_10537.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___166_10537.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___166_10537.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env _0_672 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____10540,FStar_Syntax_Syntax.Comp uu____10541) ->
                     let uu____10542 =
                       ((FStar_Syntax_Util.is_ml_comp c1) &&
                          (FStar_Syntax_Util.is_ml_comp c2))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c1) &&
                            ((FStar_Syntax_Util.is_total_comp c2) ||
                               (FStar_Syntax_Util.is_ml_comp c2))) in
                     if uu____10542
                     then
                       let _0_673 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c1)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c2) None
                           "result type" in
                       solve_t env _0_673 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Normalize.comp_to_comp_typ env c1 in
                        let c2_comp =
                          FStar_TypeChecker_Normalize.comp_to_comp_typ env c2 in
                        if
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            &&
                            (FStar_Ident.lid_equals
                               c1_comp.FStar_Syntax_Syntax.effect_name
                               c2_comp.FStar_Syntax_Syntax.effect_name)
                        then solve_eq c1_comp c2_comp
                        else
                          (let c1 =
                             FStar_TypeChecker_Normalize.unfold_effect_abbrev
                               env c1 in
                           let c2 =
                             FStar_TypeChecker_Normalize.unfold_effect_abbrev
                               env c2 in
                           (let uu____10552 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____10552
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c1.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c2.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____10554 =
                              FStar_TypeChecker_Env.monad_leq env
                                c1.FStar_Syntax_Syntax.effect_name
                                c2.FStar_Syntax_Syntax.effect_name in
                            match uu____10554 with
                            | None  ->
                                let uu____10556 =
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
                                          c2.FStar_Syntax_Syntax.result_typ)) in
                                if uu____10556
                                then
                                  let edge =
                                    {
                                      FStar_TypeChecker_Env.msource =
                                        (c1.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mtarget =
                                        (c2.FStar_Syntax_Syntax.effect_name);
                                      FStar_TypeChecker_Env.mlift =
                                        (fun r  -> fun t  -> t)
                                    } in
                                  solve_sub c1 edge c2
                                else
                                  (let _0_676 =
                                     let _0_675 =
                                       FStar_Syntax_Print.lid_to_string
                                         c1.FStar_Syntax_Syntax.effect_name in
                                     let _0_674 =
                                       FStar_Syntax_Print.lid_to_string
                                         c2.FStar_Syntax_Syntax.effect_name in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       _0_675 _0_674 in
                                   giveup env _0_676 orig)
                            | Some edge -> solve_sub c1 edge c2))))))
let print_pending_implicits: FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let _0_677 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____10584  ->
              match uu____10584 with
              | (uu____10595,uu____10596,u,uu____10598,uu____10599,uu____10600)
                  -> FStar_Syntax_Print.uvar_to_string u)) in
    FStar_All.pipe_right _0_677 (FStar_String.concat ", ")
let ineqs_to_string:
  (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let _0_678 =
        FStar_All.pipe_right (Prims.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right _0_678 (FStar_String.concat ", ") in
    let ineqs =
      let _0_681 =
        FStar_All.pipe_right (Prims.snd ineqs)
          (FStar_List.map
             (fun uu____10647  ->
                match uu____10647 with
                | (u1,u2) ->
                    let _0_680 = FStar_Syntax_Print.univ_to_string u1 in
                    let _0_679 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" _0_680 _0_679)) in
      FStar_All.pipe_right _0_681 (FStar_String.concat ", ") in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs
let guard_to_string:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.string
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Env.guard_f),
              (g.FStar_TypeChecker_Env.deferred),
              (g.FStar_TypeChecker_Env.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____10662,[])) -> "{}"
      | uu____10675 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____10685 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme) in
                if uu____10685
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry =
            let _0_682 =
              FStar_List.map
                (fun uu____10691  ->
                   match uu____10691 with
                   | (uu____10694,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred in
            FStar_All.pipe_right _0_682 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let _0_683 = ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry _0_683 imps
let guard_of_guard_formula:
  FStar_TypeChecker_Common.guard_formula -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    {
      FStar_TypeChecker_Env.guard_f = g;
      FStar_TypeChecker_Env.deferred = [];
      FStar_TypeChecker_Env.univ_ineqs = ([], []);
      FStar_TypeChecker_Env.implicits = []
    }
let guard_form:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Common.guard_formula =
  fun g  -> g.FStar_TypeChecker_Env.guard_f
let is_trivial: FStar_TypeChecker_Env.guard_t -> Prims.bool =
  fun g  ->
    match g with
    | { FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
        FStar_TypeChecker_Env.deferred = [];
        FStar_TypeChecker_Env.univ_ineqs = uu____10716;
        FStar_TypeChecker_Env.implicits = uu____10717;_} -> true
    | uu____10731 -> false
let trivial_guard: FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  }
let abstract_guard:
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
            | uu____10758 -> failwith "impossible" in
          Some
            (let uu___167_10759 = g in
             let _0_692 =
               let _0_691 =
                 let _0_690 =
                   let _0_685 = FStar_Syntax_Syntax.mk_binder x in [_0_685] in
                 let _0_689 =
                   Some
                     (let _0_688 =
                        let _0_686 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right _0_686
                          FStar_Syntax_Util.lcomp_of_comp in
                      FStar_All.pipe_right _0_688
                        (fun _0_687  -> FStar_Util.Inl _0_687)) in
                 FStar_Syntax_Util.abs _0_690 f _0_689 in
               FStar_All.pipe_left
                 (fun _0_684  -> FStar_TypeChecker_Common.NonTrivial _0_684)
                 _0_691 in
             {
               FStar_TypeChecker_Env.guard_f = _0_692;
               FStar_TypeChecker_Env.deferred =
                 (uu___167_10759.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___167_10759.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___167_10759.FStar_TypeChecker_Env.implicits)
             })
let apply_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___168_10780 = g in
          let _0_697 =
            let _0_696 =
              (FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_app
                    (let _0_695 =
                       let _0_694 = FStar_Syntax_Syntax.as_arg e in [_0_694] in
                     (f, _0_695))))
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos in
            FStar_All.pipe_left
              (fun _0_693  -> FStar_TypeChecker_Common.NonTrivial _0_693)
              _0_696 in
          {
            FStar_TypeChecker_Env.guard_f = _0_697;
            FStar_TypeChecker_Env.deferred =
              (uu___168_10780.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___168_10780.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___168_10780.FStar_TypeChecker_Env.implicits)
          }
let trivial: FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____10797 ->
        failwith "impossible"
let conj_guard_f:
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
let check_trivial:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____10815 -> FStar_TypeChecker_Common.NonTrivial t
let imp_guard_f:
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
          let imp = FStar_Syntax_Util.mk_imp f1 f2 in check_trivial imp
let binop_guard:
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
        let _0_698 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f in
        {
          FStar_TypeChecker_Env.guard_f = _0_698;
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
let conj_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard conj_guard_f g1 g2
let imp_guard:
  FStar_TypeChecker_Env.guard_t ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  = fun g1  -> fun g2  -> binop_guard imp_guard_f g1 g2
let close_guard:
  FStar_Syntax_Syntax.binders ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun binders  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___169_10883 = g in
          let _0_701 =
            let _0_700 = FStar_Syntax_Util.close_forall binders f in
            FStar_All.pipe_right _0_700
              (fun _0_699  -> FStar_TypeChecker_Common.NonTrivial _0_699) in
          {
            FStar_TypeChecker_Env.guard_f = _0_701;
            FStar_TypeChecker_Env.deferred =
              (uu___169_10883.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___169_10883.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___169_10883.FStar_TypeChecker_Env.implicits)
          }
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____10921 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel") in
    if uu____10921
    then
      let _0_703 = FStar_TypeChecker_Normalize.term_to_string env lhs in
      let _0_702 = FStar_TypeChecker_Normalize.term_to_string env rhs in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _0_703
        (rel_to_string rel) _0_702
    else "TOP" in
  let p = new_problem env lhs rel rhs elt loc reason in p
let new_t_prob:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob* FStar_Syntax_Syntax.bv)
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let _0_706 =
              let _0_705 = FStar_TypeChecker_Env.get_range env in
              FStar_All.pipe_left (fun _0_704  -> Some _0_704) _0_705 in
            FStar_Syntax_Syntax.new_bv _0_706 t1 in
          let env = FStar_TypeChecker_Env.push_bv env x in
          let p =
            let _0_710 =
              let _0_708 = FStar_Syntax_Syntax.bv_to_name x in
              FStar_All.pipe_left (fun _0_707  -> Some _0_707) _0_708 in
            let _0_709 = FStar_TypeChecker_Env.get_range env in
            new_t_problem env t1 rel t2 _0_710 _0_709 in
          ((FStar_TypeChecker_Common.TProb p), x)
let solve_and_commit:
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob* Prims.string) ->
         FStar_TypeChecker_Common.deferred Prims.option)
        -> FStar_TypeChecker_Common.deferred Prims.option
  =
  fun env  ->
    fun probs  ->
      fun err  ->
        let probs =
          let uu____10969 = FStar_Options.eager_inference () in
          if uu____10969
          then
            let uu___170_10970 = probs in
            {
              attempting = (uu___170_10970.attempting);
              wl_deferred = (uu___170_10970.wl_deferred);
              ctr = (uu___170_10970.ctr);
              defer_ok = false;
              smt_ok = (uu___170_10970.smt_ok);
              tcenv = (uu___170_10970.tcenv)
            }
          else probs in
        let tx = FStar_Unionfind.new_transaction () in
        let sol = solve env probs in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____10981 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel") in
              if uu____10981
              then
                let _0_711 = explain env d s in
                FStar_All.pipe_left FStar_Util.print_string _0_711
              else ());
             err (d, s))
let simplify_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____10991 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____10991
            then
              let _0_712 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" _0_712
            else ());
           (let f =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f in
            (let uu____10995 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____10995
             then
               let _0_713 = FStar_Syntax_Print.term_to_string f in
               FStar_Util.print1 "Simplified guard to %s\n" _0_713
             else ());
            (let f =
               let uu____10998 =
                 (FStar_Syntax_Util.unmeta f).FStar_Syntax_Syntax.n in
               match uu____10998 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____11000 -> FStar_TypeChecker_Common.NonTrivial f in
             let uu___171_11001 = g in
             {
               FStar_TypeChecker_Env.guard_f = f;
               FStar_TypeChecker_Env.deferred =
                 (uu___171_11001.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___171_11001.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___171_11001.FStar_TypeChecker_Env.implicits)
             })))
let with_guard:
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
            let _0_719 =
              let _0_718 =
                let _0_717 =
                  let _0_716 = FStar_All.pipe_right (p_guard prob) Prims.fst in
                  FStar_All.pipe_right _0_716
                    (fun _0_715  ->
                       FStar_TypeChecker_Common.NonTrivial _0_715) in
                {
                  FStar_TypeChecker_Env.guard_f = _0_717;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                } in
              simplify_guard env _0_718 in
            FStar_All.pipe_left (fun _0_714  -> Some _0_714) _0_719
let try_teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____11039 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____11039
         then
           let _0_721 = FStar_Syntax_Print.term_to_string t1 in
           let _0_720 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "try_teq of %s and %s\n" _0_721 _0_720
         else ());
        (let prob =
           let _0_724 =
             let _0_723 = FStar_TypeChecker_Env.get_range env in
             new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _0_723 in
           FStar_All.pipe_left
             (fun _0_722  -> FStar_TypeChecker_Common.TProb _0_722) _0_724 in
         let g =
           let _0_726 =
             let _0_725 = singleton env prob in
             solve_and_commit env _0_725 (fun uu____11048  -> None) in
           FStar_All.pipe_left (with_guard env prob) _0_726 in
         g)
let teq:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____11060 = try_teq env t1 t2 in
        match uu____11060 with
        | None  ->
            Prims.raise
              (FStar_Errors.Error
                 (let _0_728 =
                    FStar_TypeChecker_Err.basic_type_error env None t2 t1 in
                  let _0_727 = FStar_TypeChecker_Env.get_range env in
                  (_0_728, _0_727)))
        | Some g ->
            ((let uu____11064 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____11064
              then
                let _0_731 = FStar_Syntax_Print.term_to_string t1 in
                let _0_730 = FStar_Syntax_Print.term_to_string t2 in
                let _0_729 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" _0_731 _0_730
                  _0_729
              else ());
             g)
let try_subtype':
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____11080 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____11080
           then
             let _0_733 = FStar_TypeChecker_Normalize.term_to_string env t1 in
             let _0_732 = FStar_TypeChecker_Normalize.term_to_string env t2 in
             FStar_Util.print2 "try_subtype of %s and %s\n" _0_733 _0_732
           else ());
          (let uu____11082 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2 in
           match uu____11082 with
           | (prob,x) ->
               let g =
                 let _0_735 =
                   let _0_734 = singleton' env prob smt_ok in
                   solve_and_commit env _0_734 (fun uu____11092  -> None) in
                 FStar_All.pipe_left (with_guard env prob) _0_735 in
               ((let uu____11096 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g) in
                 if uu____11096
                 then
                   let _0_739 =
                     FStar_TypeChecker_Normalize.term_to_string env t1 in
                   let _0_738 =
                     FStar_TypeChecker_Normalize.term_to_string env t2 in
                   let _0_737 =
                     let _0_736 = FStar_Util.must g in
                     guard_to_string env _0_736 in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     _0_739 _0_738 _0_737
                 else ());
                abstract_guard x g))
let try_subtype:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t Prims.option
  = fun env  -> fun t1  -> fun t2  -> try_subtype' env t1 t2 true
let subtype_fail:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.unit
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let _0_741 = FStar_TypeChecker_Env.get_range env in
          let _0_740 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1 in
          FStar_Errors.report _0_741 _0_740
let sub_comp:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____11131 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____11131
         then
           let _0_743 = FStar_Syntax_Print.comp_to_string c1 in
           let _0_742 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print2 "sub_comp of %s and %s\n" _0_743 _0_742
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB in
         let prob =
           let _0_746 =
             let _0_745 = FStar_TypeChecker_Env.get_range env in
             new_problem env c1 rel c2 None _0_745 "sub_comp" in
           FStar_All.pipe_left
             (fun _0_744  -> FStar_TypeChecker_Common.CProb _0_744) _0_746 in
         let _0_748 =
           let _0_747 = singleton env prob in
           solve_and_commit env _0_747 (fun uu____11140  -> None) in
         FStar_All.pipe_left (with_guard env prob) _0_748)
let solve_universe_inequalities':
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list*
        (FStar_Syntax_Syntax.universe* FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____11157  ->
        match uu____11157 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              Prims.raise
                (FStar_Errors.Error
                   (let _0_752 =
                      let _0_750 = FStar_Syntax_Print.univ_to_string u1 in
                      let _0_749 = FStar_Syntax_Print.univ_to_string u2 in
                      FStar_Util.format2
                        "Universe %s and %s are incompatible" _0_750 _0_749 in
                    let _0_751 = FStar_TypeChecker_Env.get_range env in
                    (_0_752, _0_751))) in
            let equiv v v' =
              let uu____11189 =
                let _0_754 = FStar_Syntax_Subst.compress_univ v in
                let _0_753 = FStar_Syntax_Subst.compress_univ v' in
                (_0_754, _0_753) in
              match uu____11189 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____11199 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____11213 = FStar_Syntax_Subst.compress_univ v in
                      match uu____11213 with
                      | FStar_Syntax_Syntax.U_unif uu____11217 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____11228  ->
                                    match uu____11228 with
                                    | (u,v') ->
                                        let uu____11234 = equiv v v' in
                                        if uu____11234
                                        then
                                          let uu____11236 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____11236 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____11246 -> [])) in
            let uu____11249 =
              let wl =
                let uu___172_11252 = empty_worklist env in
                {
                  attempting = (uu___172_11252.attempting);
                  wl_deferred = (uu___172_11252.wl_deferred);
                  ctr = (uu___172_11252.ctr);
                  defer_ok = false;
                  smt_ok = (uu___172_11252.smt_ok);
                  tcenv = (uu___172_11252.tcenv)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____11259  ->
                      match uu____11259 with
                      | (lb,v) ->
                          let uu____11264 =
                            solve_universe_eq (- (Prims.parse_int "1")) wl lb
                              v in
                          (match uu____11264 with
                           | USolved wl -> ()
                           | uu____11266 -> fail lb v))) in
            let rec check_ineq uu____11272 =
              match uu____11272 with
              | (u,v) ->
                  let u =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u, v) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____11279) -> true
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
                       _,FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____11295) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u  -> check_ineq (u, v)))
                   | (uu____11299,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v  -> check_ineq (u, v)))
                   | uu____11304 -> false) in
            let uu____11307 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____11313  ->
                      match uu____11313 with
                      | (u,v) ->
                          let uu____11318 = check_ineq (u, v) in
                          if uu____11318
                          then true
                          else
                            ((let uu____11321 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____11321
                              then
                                let _0_756 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let _0_755 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" _0_756 _0_755
                              else ());
                             false))) in
            if uu____11307
            then ()
            else
              ((let uu____11325 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____11325
                then
                  ((let _0_757 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      _0_757);
                   FStar_Unionfind.rollback tx;
                   (let _0_758 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      _0_758))
                else ());
               Prims.raise
                 (FStar_Errors.Error
                    (let _0_759 = FStar_TypeChecker_Env.get_range env in
                     ("Failed to solve universe inequalities for inductives",
                       _0_759))))
let solve_universe_inequalities:
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list* (FStar_Syntax_Syntax.universe*
      FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Unionfind.new_transaction () in
      solve_universe_inequalities' tx env ineqs; FStar_Unionfind.commit tx
let rec solve_deferred_constraints:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____11369 =
        match uu____11369 with
        | (d,s) ->
            let msg = explain env d s in
            Prims.raise (FStar_Errors.Error (msg, (p_loc d))) in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred in
      (let uu____11379 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck") in
       if uu____11379
       then
         let _0_761 = wl_to_string wl in
         let _0_760 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits) in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           _0_761 _0_760
       else ());
      (let g =
         let uu____11391 = solve_and_commit env wl fail in
         match uu____11391 with
         | Some [] ->
             let uu___173_11398 = g in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___173_11398.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___173_11398.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___173_11398.FStar_TypeChecker_Env.implicits)
             }
         | uu____11401 ->
             failwith "impossible: Unexpected deferred constraints remain" in
       solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___174_11404 = g in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___174_11404.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___174_11404.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___174_11404.FStar_TypeChecker_Env.implicits)
        }))
let discharge_guard':
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t Prims.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g = solve_deferred_constraints env g in
          let ret_g =
            let uu___175_11430 = g in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___175_11430.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___175_11430.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___175_11430.FStar_TypeChecker_Env.implicits)
            } in
          let uu____11431 =
            Prims.op_Negation (FStar_TypeChecker_Env.should_verify env) in
          if uu____11431
          then Some ret_g
          else
            (match g.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____11437 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Norm") in
                   if uu____11437
                   then
                     let _0_764 = FStar_TypeChecker_Env.get_range env in
                     let _0_763 =
                       let _0_762 = FStar_Syntax_Print.term_to_string vc in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         _0_762 in
                     FStar_Errors.diag _0_764 _0_763
                   else ());
                  (let vc =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc in
                   match check_trivial vc with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc ->
                       if Prims.op_Negation use_smt
                       then None
                       else
                         ((let uu____11446 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel") in
                           if uu____11446
                           then
                             let _0_767 = FStar_TypeChecker_Env.get_range env in
                             let _0_766 =
                               let _0_765 =
                                 FStar_Syntax_Print.term_to_string vc in
                               FStar_Util.format1 "Checking VC=\n%s\n" _0_765 in
                             FStar_Errors.diag _0_767 _0_766
                           else ());
                          (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                            use_env_range_msg env vc;
                          Some ret_g))))
let discharge_guard:
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____11454 = discharge_guard' None env g true in
      match uu____11454 with
      | Some g -> g
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
let resolve_implicits:
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____11474 = FStar_Unionfind.find u in
      match uu____11474 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____11483 -> false in
    let rec until_fixpoint acc implicits =
      let uu____11498 = acc in
      match uu____11498 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd::tl ->
               let uu____11544 = hd in
               (match uu____11544 with
                | (uu____11551,env,u,tm,k,r) ->
                    let uu____11557 = unresolved u in
                    if uu____11557
                    then until_fixpoint ((hd :: out), changed) tl
                    else
                      (let env = FStar_TypeChecker_Env.set_expected_typ env k in
                       let tm =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env tm in
                       (let uu____11575 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelCheck") in
                        if uu____11575
                        then
                          let _0_770 = FStar_Syntax_Print.uvar_to_string u in
                          let _0_769 = FStar_Syntax_Print.term_to_string tm in
                          let _0_768 = FStar_Syntax_Print.term_to_string k in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            _0_770 _0_769 _0_768
                        else ());
                       (let uu____11580 =
                          env.FStar_TypeChecker_Env.type_of
                            (let uu___176_11584 = env in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___176_11584.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___176_11584.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___176_11584.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___176_11584.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___176_11584.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___176_11584.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___176_11584.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___176_11584.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___176_11584.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___176_11584.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___176_11584.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___176_11584.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___176_11584.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___176_11584.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___176_11584.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___176_11584.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___176_11584.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___176_11584.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___176_11584.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___176_11584.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___176_11584.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___176_11584.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___176_11584.FStar_TypeChecker_Env.qname_and_index)
                             }) tm in
                        match uu____11580 with
                        | (uu____11585,uu____11586,g) ->
                            let g =
                              if env.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___177_11589 = g in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___177_11589.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___177_11589.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___177_11589.FStar_TypeChecker_Env.implicits)
                                }
                              else g in
                            let g' =
                              let uu____11592 =
                                discharge_guard'
                                  (Some
                                     (fun uu____11596  ->
                                        FStar_Syntax_Print.term_to_string tm))
                                  env g true in
                              match uu____11592 with
                              | Some g -> g
                              | None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl)))) in
    let uu___178_11611 = g in
    let _0_771 = until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___178_11611.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___178_11611.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___178_11611.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = _0_771
    }
let force_trivial_guard:
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g =
        let _0_772 = solve_deferred_constraints env g in
        FStar_All.pipe_right _0_772 resolve_implicits in
      match g.FStar_TypeChecker_Env.implicits with
      | [] ->
          let _0_773 = discharge_guard env g in
          FStar_All.pipe_left Prims.ignore _0_773
      | (reason,uu____11639,uu____11640,e,t,r)::uu____11644 ->
          let _0_776 =
            let _0_775 = FStar_Syntax_Print.term_to_string t in
            let _0_774 = FStar_Syntax_Print.term_to_string e in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              _0_775 _0_774 reason in
          FStar_Errors.report r _0_776
let universe_inequality:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___179_11664 = trivial_guard in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___179_11664.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___179_11664.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___179_11664.FStar_TypeChecker_Env.implicits)
      }
let teq_nosmt:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____11682 = try_teq env t1 t2 in
        match uu____11682 with
        | None  -> false
        | Some g ->
            let uu____11685 = discharge_guard' None env g false in
            (match uu____11685 with
             | Some uu____11689 -> true
             | None  -> false)