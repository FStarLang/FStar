open Prims
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
        FStar_TypeChecker_Env.univ_ineqs = uu____20;
        FStar_TypeChecker_Env.implicits = uu____21;_} -> true
    | uu____35 -> false
  
let trivial_guard : FStar_TypeChecker_Env.guard_t =
  {
    FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial;
    FStar_TypeChecker_Env.deferred = [];
    FStar_TypeChecker_Env.univ_ineqs = ([], []);
    FStar_TypeChecker_Env.implicits = []
  } 
let abstract_guard :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.guard_t option ->
      FStar_TypeChecker_Env.guard_t option
  =
  fun x  ->
    fun g  ->
      match g with
      | None  -> g
      | Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____56;
            FStar_TypeChecker_Env.univ_ineqs = uu____57;
            FStar_TypeChecker_Env.implicits = uu____58;_}
          -> g
      | Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____73 -> failwith "impossible"  in
          let uu____74 =
            let uu___135_75 = g1  in
            let uu____76 =
              let uu____77 =
                let uu____78 =
                  let uu____79 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____79]  in
                FStar_Syntax_Util.abs uu____78 f
                  (Some
                     (FStar_Syntax_Util.residual_tot FStar_Syntax_Util.ktype0))
                 in
              FStar_All.pipe_left
                (fun _0_39  -> FStar_TypeChecker_Common.NonTrivial _0_39)
                uu____77
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____76;
              FStar_TypeChecker_Env.deferred =
                (uu___135_75.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___135_75.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___135_75.FStar_TypeChecker_Env.implicits)
            }  in
          Some uu____74
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___136_87 = g  in
          let uu____88 =
            let uu____89 =
              let uu____90 =
                let uu____93 =
                  let uu____94 =
                    let uu____104 =
                      let uu____106 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____106]  in
                    (f, uu____104)  in
                  FStar_Syntax_Syntax.Tm_app uu____94  in
                FStar_Syntax_Syntax.mk uu____93  in
              uu____90
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_40  -> FStar_TypeChecker_Common.NonTrivial _0_40)
              uu____89
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____88;
            FStar_TypeChecker_Env.deferred =
              (uu___136_87.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___136_87.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___136_87.FStar_TypeChecker_Env.implicits)
          }
  
let map_guard :
  FStar_TypeChecker_Env.guard_t ->
    (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
      FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun map1  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___137_128 = g  in
          let uu____129 =
            let uu____130 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____130  in
          {
            FStar_TypeChecker_Env.guard_f = uu____129;
            FStar_TypeChecker_Env.deferred =
              (uu___137_128.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___137_128.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___137_128.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____134 -> failwith "impossible"
  
let conj_guard_f :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.Trivial ,g) -> g
      | (g,FStar_TypeChecker_Common.Trivial ) -> g
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let uu____145 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____145
  
let check_trivial :
  FStar_Syntax_Syntax.term -> FStar_TypeChecker_Common.guard_formula =
  fun t  ->
    let uu____149 =
      let uu____150 = FStar_Syntax_Util.unmeta t  in
      uu____150.FStar_Syntax_Syntax.n  in
    match uu____149 with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____154 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____185 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____185;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append (fst g1.FStar_TypeChecker_Env.univ_ineqs)
                (fst g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append (snd g1.FStar_TypeChecker_Env.univ_ineqs)
                 (snd g2.FStar_TypeChecker_Env.univ_ineqs)));
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
let close_guard_univs :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun us  ->
    fun bs  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let f1 =
              FStar_List.fold_right2
                (fun u  ->
                   fun b  ->
                     fun f1  ->
                       let uu____230 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____230
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f
               in
            let uu___138_232 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___138_232.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___138_232.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___138_232.FStar_TypeChecker_Env.implicits)
            }
  
let close_forall :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder Prims.list ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun env  ->
    fun bs  ->
      fun f  ->
        FStar_List.fold_right
          (fun b  ->
             fun f1  ->
               let uu____246 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____246
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u (fst b) f1)) bs f
  
let close_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun binders  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___139_259 = g  in
            let uu____260 =
              let uu____261 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____261  in
            {
              FStar_TypeChecker_Env.guard_f = uu____260;
              FStar_TypeChecker_Env.deferred =
                (uu___139_259.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___139_259.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___139_259.FStar_TypeChecker_Env.implicits)
            }
  
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Syntax_Unionfind.fresh ()  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____289 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____304 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____304  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r
               in
            let uu____316 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____316, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____345 = FStar_Syntax_Util.type_u ()  in
        match uu____345 with
        | (t_type,u) ->
            let uu____350 =
              let uu____353 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____353 t_type  in
            (match uu____350 with
             | (tt,uu____355) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____378 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____404 -> false
  
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
    match projectee with | Success _0 -> true | uu____492 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____506 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____523 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____527 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____531 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___107_548  ->
    match uu___107_548 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____561 =
    let uu____562 = FStar_Syntax_Subst.compress t  in
    uu____562.FStar_Syntax_Syntax.n  in
  match uu____561 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____579 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____580 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____579 uu____580
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____583;
         FStar_Syntax_Syntax.pos = uu____584;
         FStar_Syntax_Syntax.vars = uu____585;_},args)
      ->
      let uu____613 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____614 = FStar_Syntax_Print.term_to_string ty  in
      let uu____615 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____613 uu____614 uu____615
  | uu____616 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___108_622  ->
      match uu___108_622 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____626 =
            let uu____628 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____629 =
              let uu____631 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____632 =
                let uu____634 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____635 =
                  let uu____637 =
                    let uu____639 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____640 =
                      let uu____642 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____643 =
                        let uu____645 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____646 =
                          let uu____648 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____648]  in
                        uu____645 :: uu____646  in
                      uu____642 :: uu____643  in
                    uu____639 :: uu____640  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____637
                   in
                uu____634 :: uu____635  in
              uu____631 :: uu____632  in
            uu____628 :: uu____629  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____626
      | FStar_TypeChecker_Common.CProb p ->
          let uu____653 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____654 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____653
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____654
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___109_660  ->
      match uu___109_660 with
      | UNIV (u,t) ->
          let x =
            let uu____664 = FStar_Options.hide_uvar_nums ()  in
            if uu____664
            then "?"
            else
              (let uu____666 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____666 FStar_Util.string_of_int)
             in
          let uu____667 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____667
      | TERM ((u,uu____669),t) ->
          let x =
            let uu____674 = FStar_Options.hide_uvar_nums ()  in
            if uu____674
            then "?"
            else
              (let uu____676 = FStar_Syntax_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____676 FStar_Util.string_of_int)
             in
          let uu____677 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____677
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____686 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____686 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____694 =
      let uu____696 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____696
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____694 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____714 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____722  ->
            match uu____722 with
            | (x,uu____726) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____714 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____731 =
      let uu____732 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____732  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____731;
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
        let uu___140_745 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___140_745.wl_deferred);
          ctr = (uu___140_745.ctr);
          defer_ok = (uu___140_745.defer_ok);
          smt_ok;
          tcenv = (uu___140_745.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___141_770 = empty_worklist env  in
  let uu____771 = FStar_List.map FStar_Pervasives.snd g  in
  {
    attempting = uu____771;
    wl_deferred = (uu___141_770.wl_deferred);
    ctr = (uu___141_770.ctr);
    defer_ok = false;
    smt_ok = (uu___141_770.smt_ok);
    tcenv = (uu___141_770.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___142_783 = wl  in
        {
          attempting = (uu___142_783.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___142_783.ctr);
          defer_ok = (uu___142_783.defer_ok);
          smt_ok = (uu___142_783.smt_ok);
          tcenv = (uu___142_783.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___143_795 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___143_795.wl_deferred);
        ctr = (uu___143_795.ctr);
        defer_ok = (uu___143_795.defer_ok);
        smt_ok = (uu___143_795.smt_ok);
        tcenv = (uu___143_795.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____806 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____806
         then
           let uu____807 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____807
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___110_811  ->
    match uu___110_811 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___144_827 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___144_827.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___144_827.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___144_827.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___144_827.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___144_827.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___144_827.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___144_827.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___111_848  ->
    match uu___111_848 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_41  -> FStar_TypeChecker_Common.TProb _0_41)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_42  -> FStar_TypeChecker_Common.CProb _0_42)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___112_864  ->
      match uu___112_864 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___113_867  ->
    match uu___113_867 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___114_876  ->
    match uu___114_876 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___115_886  ->
    match uu___115_886 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___116_896  ->
    match uu___116_896 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___117_907  ->
    match uu___117_907 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___118_918  ->
    match uu___118_918 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___119_927  ->
    match uu___119_927 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_43  -> FStar_TypeChecker_Common.TProb _0_43) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____941 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____941 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____952  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1002 = next_pid ()  in
  let uu____1003 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1002;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1003;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1050 = next_pid ()  in
  let uu____1051 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1050;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1051;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1092 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1092;
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
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort
         in
      FStar_Syntax_Util.mk_forall u x phi
  | Some e -> FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi 
let explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1144 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1144
        then
          let uu____1145 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1146 = prob_to_string env d  in
          let uu____1147 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1145 uu____1146 uu____1147 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1152 -> failwith "impossible"  in
           let uu____1153 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1161 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1162 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1161, uu____1162)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1166 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1167 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1166, uu____1167)
              in
           match uu____1153 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___120_1176  ->
            match uu___120_1176 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____1182 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM ((u,uu____1184),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___121_1197  ->
           match uu___121_1197 with
           | UNIV uu____1199 -> None
           | TERM ((u,uu____1203),t) ->
               let uu____1207 = FStar_Syntax_Unionfind.equiv uv u  in
               if uu____1207 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___122_1219  ->
           match uu___122_1219 with
           | UNIV (u',t) ->
               let uu____1223 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____1223 then Some t else None
           | uu____1226 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1233 =
        let uu____1234 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1234
         in
      FStar_Syntax_Subst.compress uu____1233
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1241 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1241
  
let norm_arg env t =
  let uu____1260 = sn env (fst t)  in (uu____1260, (snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1277  ->
              match uu____1277 with
              | (x,imp) ->
                  let uu____1284 =
                    let uu___145_1285 = x  in
                    let uu____1286 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___145_1285.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___145_1285.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1286
                    }  in
                  (uu____1284, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1301 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1301
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1304 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1304
        | uu____1306 -> u2  in
      let uu____1307 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1307
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1414 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1414 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1426;
               FStar_Syntax_Syntax.pos = uu____1427;
               FStar_Syntax_Syntax.vars = uu____1428;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1449 =
                 let uu____1450 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1451 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1450
                   uu____1451
                  in
               failwith uu____1449)
    | FStar_Syntax_Syntax.Tm_uinst uu____1461 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1488 =
             let uu____1489 = FStar_Syntax_Subst.compress t1'  in
             uu____1489.FStar_Syntax_Syntax.n  in
           match uu____1488 with
           | FStar_Syntax_Syntax.Tm_refine uu____1501 -> aux true t1'
           | uu____1506 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1518 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1541 =
             let uu____1542 = FStar_Syntax_Subst.compress t1'  in
             uu____1542.FStar_Syntax_Syntax.n  in
           match uu____1541 with
           | FStar_Syntax_Syntax.Tm_refine uu____1554 -> aux true t1'
           | uu____1559 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1571 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1603 =
             let uu____1604 = FStar_Syntax_Subst.compress t1'  in
             uu____1604.FStar_Syntax_Syntax.n  in
           match uu____1603 with
           | FStar_Syntax_Syntax.Tm_refine uu____1616 -> aux true t1'
           | uu____1621 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1633 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1645 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1657 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1669 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1681 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1700 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1721 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1741 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1760 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1787 ->
        let uu____1792 =
          let uu____1793 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1794 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1793
            uu____1794
           in
        failwith uu____1792
    | FStar_Syntax_Syntax.Tm_ascribed uu____1804 ->
        let uu____1822 =
          let uu____1823 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1824 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1823
            uu____1824
           in
        failwith uu____1822
    | FStar_Syntax_Syntax.Tm_delayed uu____1834 ->
        let uu____1849 =
          let uu____1850 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1851 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1850
            uu____1851
           in
        failwith uu____1849
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1861 =
          let uu____1862 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1863 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1862
            uu____1863
           in
        failwith uu____1861
     in
  let uu____1873 = whnf env t1  in aux false uu____1873 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1882 =
        let uu____1892 = empty_worklist env  in
        base_and_refinement env uu____1892 t  in
      FStar_All.pipe_right uu____1882 FStar_Pervasives.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____1916 = FStar_Syntax_Syntax.null_bv t  in
    (uu____1916, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____1936 = base_and_refinement env wl t  in
  match uu____1936 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____1995 =
  match uu____1995 with
  | (t_base,refopt) ->
      let uu____2009 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____2009 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___123_2033  ->
      match uu___123_2033 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2037 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2038 =
            let uu____2039 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____2039  in
          let uu____2040 =
            let uu____2041 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____2041  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2037 uu____2038
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2040
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2045 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2046 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2047 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2045 uu____2046
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2047
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____2051 =
      let uu____2053 =
        let uu____2055 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2065  ->
                  match uu____2065 with | (uu____2069,uu____2070,x) -> x))
           in
        FStar_List.append wl.attempting uu____2055  in
      FStar_List.map (wl_prob_to_string wl) uu____2053  in
    FStar_All.pipe_right uu____2051 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2088 =
          let uu____2098 =
            let uu____2099 = FStar_Syntax_Subst.compress k  in
            uu____2099.FStar_Syntax_Syntax.n  in
          match uu____2098 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2140 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2140)
              else
                (let uu____2154 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2154 with
                 | (ys',t1,uu____2170) ->
                     let uu____2173 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____2173))
          | uu____2194 ->
              let uu____2195 =
                let uu____2201 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____2201)  in
              ((ys, t), uu____2195)
           in
        match uu____2088 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Syntax_Const.effect_Tot_lid None []))
            else
              (let c1 =
                 let uu____2249 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2249 c  in
               FStar_Syntax_Util.abs ys1 t1
                 (Some (FStar_Syntax_Util.residual_comp_of_comp c1)))
  
let solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term option ->
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
            let uu____2272 = p_guard prob  in
            match uu____2272 with
            | (uu____2275,uv) ->
                ((let uu____2278 =
                    let uu____2279 = FStar_Syntax_Subst.compress uv  in
                    uu____2279.FStar_Syntax_Syntax.n  in
                  match uu____2278 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2299 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2299
                        then
                          let uu____2300 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2301 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2302 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2300
                            uu____2301 uu____2302
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2304 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___146_2307 = wl  in
                  {
                    attempting = (uu___146_2307.attempting);
                    wl_deferred = (uu___146_2307.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___146_2307.defer_ok);
                    smt_ok = (uu___146_2307.smt_ok);
                    tcenv = (uu___146_2307.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2320 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2320
         then
           let uu____2321 = FStar_Util.string_of_int pid  in
           let uu____2322 =
             let uu____2323 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2323 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2321 uu____2322
         else ());
        commit sol;
        (let uu___147_2328 = wl  in
         {
           attempting = (uu___147_2328.attempting);
           wl_deferred = (uu___147_2328.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___147_2328.defer_ok);
           smt_ok = (uu___147_2328.smt_ok);
           tcenv = (uu___147_2328.tcenv)
         })
  
let solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term option -> uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2357,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2365 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____2365
             in
          (let uu____2371 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2371
           then
             let uu____2372 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2373 =
               let uu____2374 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2374 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2372 uu____2373
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2399 =
    let uu____2403 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2403 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2399
    (FStar_Util.for_some
       (fun uu____2420  ->
          match uu____2420 with
          | (uv,uu____2424) -> FStar_Syntax_Unionfind.equiv uv (fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2457 = occurs wl uk t  in Prims.op_Negation uu____2457  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2462 =
         let uu____2463 = FStar_Syntax_Print.uvar_to_string (fst uk)  in
         let uu____2464 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2463 uu____2464
          in
       Some uu____2462)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2512 = occurs_check env wl uk t  in
  match uu____2512 with
  | (occurs_ok,msg) ->
      let uu____2529 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2529, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set1 v1  in
  let uu____2593 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2617  ->
            fun uu____2618  ->
              match (uu____2617, uu____2618) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2661 =
                    let uu____2662 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2662  in
                  if uu____2661
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2676 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2676
                     then
                       let uu____2683 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2683)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2593 with | (isect,uu____2705) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2754  ->
          fun uu____2755  ->
            match (uu____2754, uu____2755) with
            | ((a,uu____2765),(b,uu____2767)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2811 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2817  ->
                match uu____2817 with
                | (b,uu____2821) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2811 then None else Some (a, (snd hd1))
  | uu____2830 -> None 
let rec pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list ->
        FStar_Syntax_Syntax.binders option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____2873 = pat_var_opt env seen hd1  in
            (match uu____2873 with
             | None  ->
                 ((let uu____2881 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____2881
                   then
                     let uu____2882 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____2882
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____2894 =
      let uu____2895 = FStar_Syntax_Subst.compress t  in
      uu____2895.FStar_Syntax_Syntax.n  in
    match uu____2894 with
    | FStar_Syntax_Syntax.Tm_uvar uu____2898 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____2907;
           FStar_Syntax_Syntax.tk = uu____2908;
           FStar_Syntax_Syntax.pos = uu____2909;
           FStar_Syntax_Syntax.vars = uu____2910;_},uu____2911)
        -> true
    | uu____2934 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____2996;
         FStar_Syntax_Syntax.pos = uu____2997;
         FStar_Syntax_Syntax.vars = uu____2998;_},args)
      -> (t, uv, k, args)
  | uu____3039 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____3093 = destruct_flex_t t  in
  match uu____3093 with
  | (t1,uv,k,args) ->
      let uu____3161 = pat_vars env [] args  in
      (match uu____3161 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3217 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option *
  FStar_Syntax_Syntax.delta_depth option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3266 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option * FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3289 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3293 -> false
  
let head_match : match_result -> match_result =
  fun uu___124_3296  ->
    match uu___124_3296 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3305 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3318 ->
          let uu____3319 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3319 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3329 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3343 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3349 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3365 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3366 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3367 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3376 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3384 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3401) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3407,uu____3408) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3438) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3453;
             FStar_Syntax_Syntax.index = uu____3454;
             FStar_Syntax_Syntax.sort = t2;_},uu____3456)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3463 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3464 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3465 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3473 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3484 = fv_delta_depth env fv  in Some uu____3484
  
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
            let uu____3503 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3503
            then FullMatch
            else
              (let uu____3505 =
                 let uu____3510 =
                   let uu____3512 = fv_delta_depth env f  in Some uu____3512
                    in
                 let uu____3513 =
                   let uu____3515 = fv_delta_depth env g  in Some uu____3515
                    in
                 (uu____3510, uu____3513)  in
               MisMatch uu____3505)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3519),FStar_Syntax_Syntax.Tm_uinst (g,uu____3521)) ->
            let uu____3530 = head_matches env f g  in
            FStar_All.pipe_right uu____3530 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3537),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3539)) ->
            let uu____3564 = FStar_Syntax_Unionfind.equiv uv uv'  in
            if uu____3564 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3569),FStar_Syntax_Syntax.Tm_refine (y,uu____3571)) ->
            let uu____3580 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3580 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3582),uu____3583) ->
            let uu____3588 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3588 head_match
        | (uu____3589,FStar_Syntax_Syntax.Tm_refine (x,uu____3591)) ->
            let uu____3596 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3596 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3597,FStar_Syntax_Syntax.Tm_type
           uu____3598) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3599,FStar_Syntax_Syntax.Tm_arrow uu____3600) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3616),FStar_Syntax_Syntax.Tm_app (head',uu____3618))
            ->
            let uu____3647 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3647 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3649),uu____3650) ->
            let uu____3665 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3665 head_match
        | (uu____3666,FStar_Syntax_Syntax.Tm_app (head1,uu____3668)) ->
            let uu____3683 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3683 head_match
        | uu____3684 ->
            let uu____3687 =
              let uu____3692 = delta_depth_of_term env t11  in
              let uu____3694 = delta_depth_of_term env t21  in
              (uu____3692, uu____3694)  in
            MisMatch uu____3687
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3730 = FStar_Syntax_Util.head_and_args t  in
    match uu____3730 with
    | (head1,uu____3742) ->
        let uu____3757 =
          let uu____3758 = FStar_Syntax_Util.un_uinst head1  in
          uu____3758.FStar_Syntax_Syntax.n  in
        (match uu____3757 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3763 =
               let uu____3764 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3764 FStar_Option.isSome  in
             if uu____3763
             then
               let uu____3778 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3778 (fun _0_45  -> Some _0_45)
             else None
         | uu____3781 -> None)
     in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None))  in
  let fail r = (r, None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____3849) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3859 =
             let uu____3864 = maybe_inline t11  in
             let uu____3866 = maybe_inline t21  in (uu____3864, uu____3866)
              in
           match uu____3859 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____3887,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____3897 =
             let uu____3902 = maybe_inline t11  in
             let uu____3904 = maybe_inline t21  in (uu____3902, uu____3904)
              in
           match uu____3897 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____3929 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____3929 with
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
        let uu____3944 =
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
             (t11, t2'))
           in
        (match uu____3944 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____3959 -> fail r
    | uu____3964 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____3993 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4023 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4038 = FStar_Syntax_Util.type_u ()  in
      match uu____4038 with
      | (t,uu____4042) ->
          let uu____4043 = new_uvar r binders t  in fst uu____4043
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4052 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____4052 FStar_Pervasives.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      ((tc Prims.list -> FStar_Syntax_Syntax.term) *
        (FStar_Syntax_Syntax.term -> Prims.bool) *
        (FStar_Syntax_Syntax.binder option * variance * tc) Prims.list)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____4094 = head_matches env t1 t'  in
        match uu____4094 with
        | MisMatch uu____4095 -> false
        | uu____4100 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4160,imp),T (t2,uu____4163)) -> (t2, imp)
                     | uu____4180 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4220  ->
                    match uu____4220 with
                    | (t2,uu____4228) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4258 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____4258 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4311))::tcs2) ->
                       aux
                         (((let uu___148_4333 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___148_4333.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___148_4333.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4343 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___125_4374 =
                 match uu___125_4374 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____4437 = decompose1 [] bs1  in
               (rebuild, matches, uu____4437))
      | uu____4465 ->
          let rebuild uu___126_4470 =
            match uu___126_4470 with
            | [] -> t1
            | uu____4472 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___127_4491  ->
    match uu___127_4491 with
    | T (t,uu____4493) -> t
    | uu____4502 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___128_4505  ->
    match uu___128_4505 with
    | T (t,uu____4507) -> FStar_Syntax_Syntax.as_arg t
    | uu____4516 -> failwith "Impossible"
  
let imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder option * variance * tc) Prims.list ->
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
              | (uu____4585,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4604 = new_uvar r scope1 k  in
                  (match uu____4604 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4616 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r
                          in
                       let uu____4631 =
                         let uu____4632 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_46  ->
                              FStar_TypeChecker_Common.TProb _0_46)
                           uu____4632
                          in
                       ((T (gi_xs, mk_kind)), uu____4631))
              | (uu____4641,uu____4642,C uu____4643) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4730 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4741;
                         FStar_Syntax_Syntax.pos = uu____4742;
                         FStar_Syntax_Syntax.vars = uu____4743;_})
                        ->
                        let uu____4758 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4758 with
                         | (T (gi_xs,uu____4774),prob) ->
                             let uu____4784 =
                               let uu____4785 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_47  -> C _0_47)
                                 uu____4785
                                in
                             (uu____4784, [prob])
                         | uu____4787 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4797;
                         FStar_Syntax_Syntax.pos = uu____4798;
                         FStar_Syntax_Syntax.vars = uu____4799;_})
                        ->
                        let uu____4814 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4814 with
                         | (T (gi_xs,uu____4830),prob) ->
                             let uu____4840 =
                               let uu____4841 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_48  -> C _0_48)
                                 uu____4841
                                in
                             (uu____4840, [prob])
                         | uu____4843 -> failwith "impossible")
                    | (uu____4849,uu____4850,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____4852;
                         FStar_Syntax_Syntax.pos = uu____4853;
                         FStar_Syntax_Syntax.vars = uu____4854;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (None, INVARIANT,
                                    (T ((fst t), generic_kind)))))
                           in
                        let components1 =
                          (None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____4928 =
                          let uu____4933 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____4933 FStar_List.unzip
                           in
                        (match uu____4928 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____4962 =
                                 let uu____4963 =
                                   let uu____4966 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____4966 un_T  in
                                 let uu____4967 =
                                   let uu____4973 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____4973
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____4963;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____4967;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____4962
                                in
                             ((C gi_xs), sub_probs))
                    | uu____4978 ->
                        let uu____4985 = sub_prob scope1 args q  in
                        (match uu____4985 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____4730 with
                   | (tc,probs) ->
                       let uu____5003 =
                         match q with
                         | (Some b,uu____5029,uu____5030) ->
                             let uu____5038 =
                               let uu____5042 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____5042 :: args  in
                             ((Some b), (b :: scope1), uu____5038)
                         | uu____5060 -> (None, scope1, args)  in
                       (match uu____5003 with
                        | (bopt,scope2,args1) ->
                            let uu____5103 = aux scope2 args1 qs2  in
                            (match uu____5103 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5124 =
                                         let uu____5126 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         f :: uu____5126  in
                                       FStar_Syntax_Util.mk_conj_l uu____5124
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____5139 =
                                         let uu____5141 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f
                                            in
                                         let uu____5142 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         uu____5141 :: uu____5142  in
                                       FStar_Syntax_Util.mk_conj_l uu____5139
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
    option * variance * tc) Prims.list))
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___149_5195 = p  in
  let uu____5198 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____5199 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___149_5195.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5198;
    FStar_TypeChecker_Common.relation =
      (uu___149_5195.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5199;
    FStar_TypeChecker_Common.element =
      (uu___149_5195.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___149_5195.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___149_5195.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___149_5195.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___149_5195.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___149_5195.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5209 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____5209
            (fun _0_49  -> FStar_TypeChecker_Common.TProb _0_49)
      | FStar_TypeChecker_Common.CProb uu____5214 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5228 = compress_prob wl pr  in
        FStar_All.pipe_right uu____5228 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5234 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____5234 with
           | (lh,uu____5247) ->
               let uu____5262 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____5262 with
                | (rh,uu____5275) ->
                    let uu____5290 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5299,FStar_Syntax_Syntax.Tm_uvar uu____5300)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5319,uu____5320)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5331,FStar_Syntax_Syntax.Tm_uvar uu____5332)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5343,uu____5344)
                          ->
                          let uu____5353 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5353 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5393 ->
                                    let rank =
                                      let uu____5400 = is_top_level_prob prob
                                         in
                                      if uu____5400
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5402 =
                                      let uu___150_5405 = tp  in
                                      let uu____5408 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___150_5405.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___150_5405.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___150_5405.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5408;
                                        FStar_TypeChecker_Common.element =
                                          (uu___150_5405.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___150_5405.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___150_5405.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___150_5405.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___150_5405.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___150_5405.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5402)))
                      | (uu____5418,FStar_Syntax_Syntax.Tm_uvar uu____5419)
                          ->
                          let uu____5428 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5428 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5468 ->
                                    let uu____5474 =
                                      let uu___151_5479 = tp  in
                                      let uu____5482 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___151_5479.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5482;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___151_5479.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___151_5479.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___151_5479.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___151_5479.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___151_5479.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___151_5479.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___151_5479.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___151_5479.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5474)))
                      | (uu____5498,uu____5499) -> (rigid_rigid, tp)  in
                    (match uu____5290 with
                     | (rank,tp1) ->
                         let uu____5510 =
                           FStar_All.pipe_right
                             (let uu___152_5513 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___152_5513.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___152_5513.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___152_5513.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___152_5513.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___152_5513.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___152_5513.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___152_5513.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___152_5513.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___152_5513.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_50  ->
                                FStar_TypeChecker_Common.TProb _0_50)
                            in
                         (rank, uu____5510))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5519 =
            FStar_All.pipe_right
              (let uu___153_5522 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___153_5522.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___153_5522.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___153_5522.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___153_5522.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___153_5522.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___153_5522.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___153_5522.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___153_5522.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___153_5522.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_51  -> FStar_TypeChecker_Common.CProb _0_51)
             in
          (rigid_rigid, uu____5519)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob option * FStar_TypeChecker_Common.prob
      Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____5554 probs =
      match uu____5554 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5584 = rank wl hd1  in
               (match uu____5584 with
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
    match projectee with | UDeferred _0 -> true | uu____5652 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5664 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5676 -> false
  
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
                        let uu____5709 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5709 with
                        | (k,uu____5713) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____5717 -> false)))
            | uu____5718 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5761 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5761 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5764 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5770 =
                     let uu____5771 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5772 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5771
                       uu____5772
                      in
                   UFailed uu____5770)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5788 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5788 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5806 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5806 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5809 ->
                let uu____5812 =
                  let uu____5813 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____5814 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____5813
                    uu____5814 msg
                   in
                UFailed uu____5812
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____5815,uu____5816) ->
              let uu____5817 =
                let uu____5818 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5819 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5818 uu____5819
                 in
              failwith uu____5817
          | (FStar_Syntax_Syntax.U_unknown ,uu____5820) ->
              let uu____5821 =
                let uu____5822 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5823 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5822 uu____5823
                 in
              failwith uu____5821
          | (uu____5824,FStar_Syntax_Syntax.U_bvar uu____5825) ->
              let uu____5826 =
                let uu____5827 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5828 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5827 uu____5828
                 in
              failwith uu____5826
          | (uu____5829,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____5830 =
                let uu____5831 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____5832 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____5831 uu____5832
                 in
              failwith uu____5830
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____5844 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____5844
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____5854 = occurs_univ v1 u3  in
              if uu____5854
              then
                let uu____5855 =
                  let uu____5856 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____5857 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5856 uu____5857
                   in
                try_umax_components u11 u21 uu____5855
              else
                (let uu____5859 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____5859)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____5867 = occurs_univ v1 u3  in
              if uu____5867
              then
                let uu____5868 =
                  let uu____5869 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____5870 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____5869 uu____5870
                   in
                try_umax_components u11 u21 uu____5868
              else
                (let uu____5872 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____5872)
          | (FStar_Syntax_Syntax.U_max uu____5875,uu____5876) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____5881 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____5881
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____5883,FStar_Syntax_Syntax.U_max uu____5884) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____5889 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____5889
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____5891,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____5892,FStar_Syntax_Syntax.U_name
             uu____5893) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____5894) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____5895) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5896,FStar_Syntax_Syntax.U_succ
             uu____5897) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____5898,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
  
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
  let uu____5960 = bc1  in
  match uu____5960 with
  | (bs1,mk_cod1) ->
      let uu____5985 = bc2  in
      (match uu____5985 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6032 = FStar_Util.first_N n1 bs  in
             match uu____6032 with
             | (bs3,rest) ->
                 let uu____6046 = mk_cod rest  in (bs3, uu____6046)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____6064 =
               let uu____6068 = mk_cod1 []  in (bs1, uu____6068)  in
             let uu____6070 =
               let uu____6074 = mk_cod2 []  in (bs2, uu____6074)  in
             (uu____6064, uu____6070)
           else
             if l1 > l2
             then
               (let uu____6096 = curry l2 bs1 mk_cod1  in
                let uu____6103 =
                  let uu____6107 = mk_cod2 []  in (bs2, uu____6107)  in
                (uu____6096, uu____6103))
             else
               (let uu____6116 =
                  let uu____6120 = mk_cod1 []  in (bs1, uu____6120)  in
                let uu____6122 = curry l1 bs2 mk_cod2  in
                (uu____6116, uu____6122)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6226 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____6226
       then
         let uu____6227 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6227
       else ());
      (let uu____6229 = next_prob probs  in
       match uu____6229 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___154_6242 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___154_6242.wl_deferred);
               ctr = (uu___154_6242.ctr);
               defer_ok = (uu___154_6242.defer_ok);
               smt_ok = (uu___154_6242.smt_ok);
               tcenv = (uu___154_6242.tcenv)
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
                  let uu____6249 = solve_flex_rigid_join env tp probs1  in
                  (match uu____6249 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6253 = solve_rigid_flex_meet env tp probs1  in
                     match uu____6253 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6257,uu____6258) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6267 ->
                let uu____6272 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6300  ->
                          match uu____6300 with
                          | (c,uu____6305,uu____6306) -> c < probs.ctr))
                   in
                (match uu____6272 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6328 =
                            FStar_List.map
                              (fun uu____6334  ->
                                 match uu____6334 with
                                 | (uu____6340,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____6328
                      | uu____6343 ->
                          let uu____6348 =
                            let uu___155_6349 = probs  in
                            let uu____6350 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6359  ->
                                      match uu____6359 with
                                      | (uu____6363,uu____6364,y) -> y))
                               in
                            {
                              attempting = uu____6350;
                              wl_deferred = rest;
                              ctr = (uu___155_6349.ctr);
                              defer_ok = (uu___155_6349.defer_ok);
                              smt_ok = (uu___155_6349.smt_ok);
                              tcenv = (uu___155_6349.tcenv)
                            }  in
                          solve env uu____6348))))

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
            let uu____6371 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____6371 with
            | USolved wl1 ->
                let uu____6373 = solve_prob orig None [] wl1  in
                solve env uu____6373
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
                  let uu____6407 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6407 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6410 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6418;
                  FStar_Syntax_Syntax.pos = uu____6419;
                  FStar_Syntax_Syntax.vars = uu____6420;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6423;
                  FStar_Syntax_Syntax.pos = uu____6424;
                  FStar_Syntax_Syntax.vars = uu____6425;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6437,uu____6438) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6443,FStar_Syntax_Syntax.Tm_uinst uu____6444) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6449 -> USolved wl

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
            ((let uu____6457 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6457
              then
                let uu____6458 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6458 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6466 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6466
         then
           let uu____6467 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6467
         else ());
        (let uu____6469 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6469 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6511 = head_matches_delta env () t1 t2  in
               match uu____6511 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6533 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6559 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6568 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6569 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6568, uu____6569)
                          | None  ->
                              let uu____6572 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6573 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6572, uu____6573)
                           in
                        (match uu____6559 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6595 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_52  ->
                                    FStar_TypeChecker_Common.TProb _0_52)
                                 uu____6595
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6618 =
                                    let uu____6624 =
                                      let uu____6627 =
                                        let uu____6630 =
                                          let uu____6631 =
                                            let uu____6636 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____6636)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6631
                                           in
                                        FStar_Syntax_Syntax.mk uu____6630  in
                                      uu____6627 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6649 =
                                      let uu____6651 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____6651]  in
                                    (uu____6624, uu____6649)  in
                                  Some uu____6618
                              | (uu____6660,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6662)) ->
                                  let uu____6667 =
                                    let uu____6671 =
                                      let uu____6673 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____6673]  in
                                    (t11, uu____6671)  in
                                  Some uu____6667
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6679),uu____6680) ->
                                  let uu____6685 =
                                    let uu____6689 =
                                      let uu____6691 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____6691]  in
                                    (t21, uu____6689)  in
                                  Some uu____6685
                              | uu____6696 ->
                                  let uu____6699 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____6699 with
                                   | (head1,uu____6714) ->
                                       let uu____6729 =
                                         let uu____6730 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6730.FStar_Syntax_Syntax.n  in
                                       (match uu____6729 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6737;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6739;_}
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
                                        | uu____6748 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6757) ->
                  let uu____6770 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___129_6779  ->
                            match uu___129_6779 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6784 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6784 with
                                      | (u',uu____6795) ->
                                          let uu____6810 =
                                            let uu____6811 = whnf env u'  in
                                            uu____6811.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____6810 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____6815) ->
                                               FStar_Syntax_Unionfind.equiv
                                                 uv uv'
                                           | uu____6828 -> false))
                                 | uu____6829 -> false)
                            | uu____6831 -> false))
                     in
                  (match uu____6770 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____6852 tps =
                         match uu____6852 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____6879 =
                                    let uu____6884 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____6884  in
                                  (match uu____6879 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____6903 -> None)
                          in
                       let uu____6908 =
                         let uu____6913 =
                           let uu____6917 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____6917, [])  in
                         make_lower_bound uu____6913 lower_bounds  in
                       (match uu____6908 with
                        | None  ->
                            ((let uu____6924 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6924
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
                            ((let uu____6937 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____6937
                              then
                                let wl' =
                                  let uu___156_6939 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___156_6939.wl_deferred);
                                    ctr = (uu___156_6939.ctr);
                                    defer_ok = (uu___156_6939.defer_ok);
                                    smt_ok = (uu___156_6939.smt_ok);
                                    tcenv = (uu___156_6939.tcenv)
                                  }  in
                                let uu____6940 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____6940
                              else ());
                             (let uu____6942 =
                                solve_t env eq_prob
                                  (let uu___157_6943 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___157_6943.wl_deferred);
                                     ctr = (uu___157_6943.ctr);
                                     defer_ok = (uu___157_6943.defer_ok);
                                     smt_ok = (uu___157_6943.smt_ok);
                                     tcenv = (uu___157_6943.tcenv)
                                   })
                                 in
                              match uu____6942 with
                              | Success uu____6945 ->
                                  let wl1 =
                                    let uu___158_6947 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___158_6947.wl_deferred);
                                      ctr = (uu___158_6947.ctr);
                                      defer_ok = (uu___158_6947.defer_ok);
                                      smt_ok = (uu___158_6947.smt_ok);
                                      tcenv = (uu___158_6947.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____6949 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____6952 -> None))))
              | uu____6953 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6960 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6960
         then
           let uu____6961 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____6961
         else ());
        (let uu____6963 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____6963 with
         | (u,args) ->
             let uu____6990 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____6990 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____7021 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____7021 with
                    | (h1,args1) ->
                        let uu____7049 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____7049 with
                         | (h2,uu____7062) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7081 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____7081
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7094 =
                                          let uu____7096 =
                                            let uu____7097 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_53  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_53) uu____7097
                                             in
                                          [uu____7096]  in
                                        Some uu____7094))
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
                                       (let uu____7119 =
                                          let uu____7121 =
                                            let uu____7122 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_54  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_54) uu____7122
                                             in
                                          [uu____7121]  in
                                        Some uu____7119))
                                  else None
                              | uu____7130 -> None))
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
                             let uu____7196 =
                               let uu____7202 =
                                 let uu____7205 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____7205  in
                               (uu____7202, m1)  in
                             Some uu____7196)
                    | (uu____7214,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7216)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7248),uu____7249) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7280 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7314) ->
                       let uu____7327 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___130_7336  ->
                                 match uu___130_7336 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7341 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____7341 with
                                           | (u',uu____7352) ->
                                               let uu____7367 =
                                                 let uu____7368 = whnf env u'
                                                    in
                                                 uu____7368.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7367 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7372) ->
                                                    FStar_Syntax_Unionfind.equiv
                                                      uv uv'
                                                | uu____7385 -> false))
                                      | uu____7386 -> false)
                                 | uu____7388 -> false))
                          in
                       (match uu____7327 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7413 tps =
                              match uu____7413 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7454 =
                                         let uu____7461 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7461  in
                                       (match uu____7454 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7496 -> None)
                               in
                            let uu____7503 =
                              let uu____7510 =
                                let uu____7516 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7516, [])  in
                              make_upper_bound uu____7510 upper_bounds  in
                            (match uu____7503 with
                             | None  ->
                                 ((let uu____7525 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7525
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
                                 ((let uu____7544 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7544
                                   then
                                     let wl' =
                                       let uu___159_7546 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___159_7546.wl_deferred);
                                         ctr = (uu___159_7546.ctr);
                                         defer_ok = (uu___159_7546.defer_ok);
                                         smt_ok = (uu___159_7546.smt_ok);
                                         tcenv = (uu___159_7546.tcenv)
                                       }  in
                                     let uu____7547 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7547
                                   else ());
                                  (let uu____7549 =
                                     solve_t env eq_prob
                                       (let uu___160_7550 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___160_7550.wl_deferred);
                                          ctr = (uu___160_7550.ctr);
                                          defer_ok = (uu___160_7550.defer_ok);
                                          smt_ok = (uu___160_7550.smt_ok);
                                          tcenv = (uu___160_7550.tcenv)
                                        })
                                      in
                                   match uu____7549 with
                                   | Success uu____7552 ->
                                       let wl1 =
                                         let uu___161_7554 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___161_7554.wl_deferred);
                                           ctr = (uu___161_7554.ctr);
                                           defer_ok =
                                             (uu___161_7554.defer_ok);
                                           smt_ok = (uu___161_7554.smt_ok);
                                           tcenv = (uu___161_7554.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____7556 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____7559 -> None))))
                   | uu____7560 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____7625 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____7625
                      then
                        let uu____7626 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7626
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___162_7658 = hd1  in
                      let uu____7659 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___162_7658.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___162_7658.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7659
                      }  in
                    let hd21 =
                      let uu___163_7663 = hd2  in
                      let uu____7664 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___163_7663.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___163_7663.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7664
                      }  in
                    let prob =
                      let uu____7668 =
                        let uu____7671 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7671 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_55  -> FStar_TypeChecker_Common.TProb _0_55)
                        uu____7668
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____7679 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7679
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____7682 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____7682 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7700 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst
                              in
                           let uu____7703 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____7700 uu____7703
                            in
                         ((let uu____7709 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7709
                           then
                             let uu____7710 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7711 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7710 uu____7711
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7726 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7732 = aux scope env [] bs1 bs2  in
              match uu____7732 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7748 = compress_tprob wl problem  in
        solve_t' env uu____7748 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7781 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7781 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7798,uu____7799) ->
                   let may_relate head3 =
                     let uu____7814 =
                       let uu____7815 = FStar_Syntax_Util.un_uinst head3  in
                       uu____7815.FStar_Syntax_Syntax.n  in
                     match uu____7814 with
                     | FStar_Syntax_Syntax.Tm_name uu____7818 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____7819 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____7836 -> false  in
                   let uu____7837 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____7837
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
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11
                                   in
                                let uu____7854 =
                                  let uu____7855 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____7855 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____7854
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____7857 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____7857
                   else
                     (let uu____7859 =
                        let uu____7860 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____7861 =
                          FStar_Syntax_Print.term_to_string head2  in
                        FStar_Util.format2 "head mismatch (%s vs %s)"
                          uu____7860 uu____7861
                         in
                      giveup env1 uu____7859 orig)
               | (uu____7862,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___164_7870 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___164_7870.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___164_7870.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___164_7870.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___164_7870.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___164_7870.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___164_7870.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___164_7870.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___164_7870.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____7871,None ) ->
                   ((let uu____7878 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____7878
                     then
                       let uu____7879 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____7880 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____7881 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____7882 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____7879
                         uu____7880 uu____7881 uu____7882
                     else ());
                    (let uu____7884 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____7884 with
                     | (head11,args1) ->
                         let uu____7910 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____7910 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____7950 =
                                  let uu____7951 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____7952 = args_to_string args1  in
                                  let uu____7953 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____7954 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____7951 uu____7952 uu____7953
                                    uu____7954
                                   in
                                giveup env1 uu____7950 orig
                              else
                                (let uu____7956 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____7959 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____7959 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____7956
                                 then
                                   let uu____7960 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____7960 with
                                   | USolved wl2 ->
                                       let uu____7962 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____7962
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____7966 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____7966 with
                                    | (base1,refinement1) ->
                                        let uu____7992 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____7992 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8046 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____8046 with
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
                                                           (fun uu____8056 
                                                              ->
                                                              fun uu____8057 
                                                                ->
                                                                match 
                                                                  (uu____8056,
                                                                    uu____8057)
                                                                with
                                                                | ((a,uu____8067),
                                                                   (a',uu____8069))
                                                                    ->
                                                                    let uu____8074
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
                                                                    _0_56  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_56)
                                                                    uu____8074)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____8080 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8080
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8084 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___165_8117 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___165_8117.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____8137 = p  in
          match uu____8137 with
          | (((u,k),xs,c),ps,(h,uu____8148,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8197 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____8197 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8211 = h gs_xs  in
                     let uu____8212 =
                       FStar_All.pipe_right
                         (FStar_Syntax_Util.residual_comp_of_comp c)
                         (fun _0_57  -> Some _0_57)
                        in
                     FStar_Syntax_Util.abs xs1 uu____8211 uu____8212  in
                   ((let uu____8216 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8216
                     then
                       let uu____8217 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____8218 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____8219 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____8220 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____8221 =
                         let uu____8222 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____8222
                           (FStar_String.concat ", ")
                          in
                       let uu____8225 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8217 uu____8218 uu____8219 uu____8220
                         uu____8221 uu____8225
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___131_8243 =
          match uu___131_8243 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____8272 = p  in
          match uu____8272 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8330 = FStar_List.nth ps i  in
              (match uu____8330 with
               | (pi,uu____8333) ->
                   let uu____8338 = FStar_List.nth xs i  in
                   (match uu____8338 with
                    | (xi,uu____8345) ->
                        let rec gs k =
                          let uu____8354 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____8354 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8406)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8414 = new_uvar r xs k_a  in
                                    (match uu____8414 with
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
                                         let uu____8433 = aux subst2 tl1  in
                                         (match uu____8433 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8448 =
                                                let uu____8450 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8450 :: gi_xs'  in
                                              let uu____8451 =
                                                let uu____8453 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8453 :: gi_ps'  in
                                              (uu____8448, uu____8451)))
                                 in
                              aux [] bs
                           in
                        let uu____8456 =
                          let uu____8457 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8457
                           in
                        if uu____8456
                        then None
                        else
                          (let uu____8460 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8460 with
                           | (g_xs,uu____8467) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8474 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 let uu____8479 =
                                   FStar_All.pipe_right
                                     (FStar_Syntax_Util.residual_comp_of_comp
                                        c) (fun _0_58  -> Some _0_58)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8474
                                   uu____8479
                                  in
                               let sub1 =
                                 let uu____8483 =
                                   let uu____8486 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____8493 =
                                     let uu____8496 =
                                       FStar_List.map
                                         (fun uu____8502  ->
                                            match uu____8502 with
                                            | (uu____8507,uu____8508,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8496  in
                                   mk_problem (p_scope orig) orig uu____8486
                                     (p_rel orig) uu____8493 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_59  ->
                                      FStar_TypeChecker_Common.TProb _0_59)
                                   uu____8483
                                  in
                               ((let uu____8518 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8518
                                 then
                                   let uu____8519 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8520 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8519 uu____8520
                                 else ());
                                (let wl2 =
                                   let uu____8523 =
                                     let uu____8525 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1)
                                        in
                                     Some uu____8525  in
                                   solve_prob orig uu____8523
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8530 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_60  -> Some _0_60) uu____8530)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8554 = lhs  in
          match uu____8554 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8577 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8577 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8599 =
                        let uu____8625 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____8625)  in
                      Some uu____8599
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____8708 =
                           let uu____8712 =
                             let uu____8713 = FStar_Syntax_Subst.compress k
                                in
                             uu____8713.FStar_Syntax_Syntax.n  in
                           (uu____8712, args)  in
                         match uu____8708 with
                         | (uu____8720,[]) ->
                             let uu____8722 =
                               let uu____8728 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____8728)  in
                             Some uu____8722
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____8739,uu____8740) ->
                             let uu____8751 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____8751 with
                              | (uv1,uv_args) ->
                                  let uu____8780 =
                                    let uu____8781 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____8781.FStar_Syntax_Syntax.n  in
                                  (match uu____8780 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8788) ->
                                       let uu____8801 =
                                         pat_vars env [] uv_args  in
                                       (match uu____8801 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8815  ->
                                                      let uu____8816 =
                                                        let uu____8817 =
                                                          let uu____8818 =
                                                            let uu____8821 =
                                                              let uu____8822
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8822
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8821
                                                             in
                                                          fst uu____8818  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8817
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8816))
                                               in
                                            let c1 =
                                              let uu____8828 =
                                                let uu____8829 =
                                                  let uu____8832 =
                                                    let uu____8833 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8833
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8832
                                                   in
                                                fst uu____8829  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8828
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____8842 =
                                                let uu____8844 =
                                                  let uu____8845 =
                                                    let uu____8848 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8848
                                                      FStar_Pervasives.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____8845
                                                   in
                                                Some uu____8844  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8842
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____8858 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____8861,uu____8862)
                             ->
                             let uu____8874 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____8874 with
                              | (uv1,uv_args) ->
                                  let uu____8903 =
                                    let uu____8904 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____8904.FStar_Syntax_Syntax.n  in
                                  (match uu____8903 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____8911) ->
                                       let uu____8924 =
                                         pat_vars env [] uv_args  in
                                       (match uu____8924 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____8938  ->
                                                      let uu____8939 =
                                                        let uu____8940 =
                                                          let uu____8941 =
                                                            let uu____8944 =
                                                              let uu____8945
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____8945
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____8944
                                                             in
                                                          fst uu____8941  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____8940
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____8939))
                                               in
                                            let c1 =
                                              let uu____8951 =
                                                let uu____8952 =
                                                  let uu____8955 =
                                                    let uu____8956 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8956
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____8955
                                                   in
                                                fst uu____8952  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____8951
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____8965 =
                                                let uu____8967 =
                                                  let uu____8968 =
                                                    let uu____8971 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____8971
                                                      FStar_Pervasives.fst
                                                     in
                                                  FStar_Syntax_Util.residual_tot
                                                    uu____8968
                                                   in
                                                Some uu____8967  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____8965
                                               in
                                            (FStar_Syntax_Unionfind.change
                                               uvar uv_sol;
                                             Some (xs1, c1)))
                                   | uu____8981 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____8986)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____9012 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____9012
                                 (fun _0_61  -> Some _0_61)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9031 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____9031 with
                                  | (args1,rest) ->
                                      let uu____9047 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____9047 with
                                       | (xs2,c2) ->
                                           let uu____9055 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____9055
                                             (fun uu____9066  ->
                                                match uu____9066 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9088 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____9088 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9134 =
                                        let uu____9137 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9137
                                         in
                                      FStar_All.pipe_right uu____9134
                                        (fun _0_62  -> Some _0_62))
                         | uu____9145 ->
                             let uu____9149 =
                               let uu____9150 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____9151 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____9152 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9150 uu____9151 uu____9152
                                in
                             failwith uu____9149
                          in
                       let uu____9156 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____9156
                         (fun uu____9184  ->
                            match uu____9184 with
                            | (xs1,c1) ->
                                let uu____9212 =
                                  let uu____9235 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9235)
                                   in
                                Some uu____9212))
                 in
              let rec imitate_or_project n1 stopt i =
                if (i >= n1) || (FStar_Option.isNone stopt)
                then
                  giveup env
                    "flex-rigid case failed all backtracking attempts" orig
                else
                  (let st = FStar_Option.get stopt  in
                   let tx = FStar_Syntax_Unionfind.new_transaction ()  in
                   if i = (~- (Prims.parse_int "1"))
                   then
                     let uu____9307 = imitate orig env wl1 st  in
                     match uu____9307 with
                     | Failed uu____9312 ->
                         (FStar_Syntax_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9318 = project orig env wl1 i st  in
                      match uu____9318 with
                      | None  ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9325) ->
                          (FStar_Syntax_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____9339 = FStar_Syntax_Util.head_and_args t21  in
                match uu____9339 with
                | (hd1,uu____9350) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9365 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9373 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9374 -> true
                     | uu____9384 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____9387 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____9387
                         then true
                         else
                           ((let uu____9390 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____9390
                             then
                               let uu____9391 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9391
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9399 =
                    let uu____9402 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____9402 FStar_Pervasives.fst  in
                  FStar_All.pipe_right uu____9399 FStar_Syntax_Free.names  in
                let uu____9433 = FStar_Util.set_is_empty fvs_hd  in
                if uu____9433
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____9442 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____9442 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9450 =
                            let uu____9451 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____9451
                             in
                          giveup_or_defer1 orig uu____9450
                        else
                          (let uu____9453 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____9453
                           then
                             let uu____9454 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____9454
                              then
                                let uu____9455 = subterms args_lhs  in
                                imitate' orig env wl1 uu____9455
                              else
                                ((let uu____9459 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____9459
                                  then
                                    let uu____9460 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9461 = names_to_string fvs1  in
                                    let uu____9462 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9460 uu____9461 uu____9462
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9467 ->
                                        let uu____9468 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9468 t21
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
                               (let uu____9477 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9477
                                then
                                  ((let uu____9479 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9479
                                    then
                                      let uu____9480 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9481 = names_to_string fvs1
                                         in
                                      let uu____9482 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9480 uu____9481 uu____9482
                                    else ());
                                   (let uu____9484 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9484
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
                     (let uu____9495 =
                        let uu____9496 = FStar_Syntax_Free.names t1  in
                        check_head uu____9496 t2  in
                      if uu____9495
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9500 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9500
                          then
                            let uu____9501 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9501
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9504 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9504 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9546 =
               match uu____9546 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k
                      in
                   let uu____9577 = FStar_Syntax_Util.arrow_formals k1  in
                   (match uu____9577 with
                    | (all_formals,uu____9588) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____9680  ->
                                        match uu____9680 with
                                        | (x,imp) ->
                                            let uu____9687 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____9687, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____9695 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____9695 with
                                | (t1,uu____9699) ->
                                    let uu____9700 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    fst uu____9700
                                 in
                              let uu____9703 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____9703 with
                               | (t',tm_u1) ->
                                   let uu____9710 = destruct_flex_t t'  in
                                   (match uu____9710 with
                                    | (uu____9730,u1,k11,uu____9733) ->
                                        let sol =
                                          let uu____9761 =
                                            let uu____9766 =
                                              u_abs k1 all_formals t'  in
                                            ((u, k1), uu____9766)  in
                                          TERM uu____9761  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____9826 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____9826 with
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
                                              (fun uu____9855  ->
                                                 match uu____9855 with
                                                 | (x,uu____9859) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x (fst y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____9865 =
                                        let uu____9866 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____9866  in
                                      if uu____9865
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____9870 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____9870 formals1
                                           tl1)))
                          | uu____9876 -> failwith "Impossible"  in
                        let uu____9887 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____9887 all_formals args)
                in
             let solve_both_pats wl1 uu____9927 uu____9928 r =
               match (uu____9927, uu____9928) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10042 =
                     (FStar_Syntax_Unionfind.equiv u1 u2) &&
                       (binders_eq xs ys)
                      in
                   if uu____10042
                   then
                     let uu____10043 = solve_prob orig None [] wl1  in
                     solve env uu____10043
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____10058 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10058
                       then
                         let uu____10059 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____10060 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____10061 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____10062 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____10063 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10059 uu____10060 uu____10061 uu____10062
                           uu____10063
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____10105 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____10105 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10113 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____10113 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10143 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10143
                                     in
                                  let uu____10146 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____10146 k3)
                           else
                             (let uu____10149 =
                                let uu____10150 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____10151 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____10152 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10150 uu____10151 uu____10152
                                 in
                              failwith uu____10149)
                          in
                       let uu____10153 =
                         let uu____10159 =
                           let uu____10167 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____10167  in
                         match uu____10159 with
                         | (bs,k1') ->
                             let uu____10185 =
                               let uu____10193 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____10193
                                in
                             (match uu____10185 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____10214 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_63  ->
                                         FStar_TypeChecker_Common.TProb _0_63)
                                      uu____10214
                                     in
                                  let uu____10219 =
                                    let uu____10222 =
                                      let uu____10223 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____10223.FStar_Syntax_Syntax.n  in
                                    let uu____10226 =
                                      let uu____10227 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____10227.FStar_Syntax_Syntax.n  in
                                    (uu____10222, uu____10226)  in
                                  (match uu____10219 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10235,uu____10236) ->
                                       (k1', [sub_prob])
                                   | (uu____10240,FStar_Syntax_Syntax.Tm_type
                                      uu____10241) -> (k2', [sub_prob])
                                   | uu____10245 ->
                                       let uu____10248 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____10248 with
                                        | (t,uu____10257) ->
                                            let uu____10258 = new_uvar r zs t
                                               in
                                            (match uu____10258 with
                                             | (k_zs,uu____10267) ->
                                                 let kprob =
                                                   let uu____10269 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_64  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_64) uu____10269
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____10153 with
                       | (k_u',sub_probs) ->
                           let uu____10283 =
                             let uu____10291 =
                               let uu____10292 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10292
                                in
                             let uu____10297 =
                               let uu____10300 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____10300  in
                             let uu____10303 =
                               let uu____10306 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____10306  in
                             (uu____10291, uu____10297, uu____10303)  in
                           (match uu____10283 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____10325 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____10325 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____10337 =
                                          FStar_Syntax_Unionfind.equiv u1 u2
                                           in
                                        if uu____10337
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____10341 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____10341 with
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
             let solve_one_pat uu____10373 uu____10374 =
               match (uu____10373, uu____10374) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10438 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10438
                     then
                       let uu____10439 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10440 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10439 uu____10440
                     else ());
                    (let uu____10442 = FStar_Syntax_Unionfind.equiv u1 u2  in
                     if uu____10442
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10449  ->
                              fun uu____10450  ->
                                match (uu____10449, uu____10450) with
                                | ((a,uu____10460),(t21,uu____10462)) ->
                                    let uu____10467 =
                                      let uu____10470 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10470
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10467
                                      (fun _0_65  ->
                                         FStar_TypeChecker_Common.TProb _0_65))
                           xs args2
                          in
                       let guard =
                         let uu____10474 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10474  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10484 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10484 with
                        | (occurs_ok,uu____10489) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10494 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10494
                            then
                              let sol =
                                let uu____10496 =
                                  let uu____10501 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10501)  in
                                TERM uu____10496  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____10506 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____10506
                               then
                                 let uu____10507 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____10507 with
                                 | (sol,(uu____10517,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____10527 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____10527
                                       then
                                         let uu____10528 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10528
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____10533 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____10535 = lhs  in
             match uu____10535 with
             | (t1,u1,k1,args1) ->
                 let uu____10540 = rhs  in
                 (match uu____10540 with
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
                       | uu____10566 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____10572 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____10572 with
                              | (sol,uu____10579) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____10582 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____10582
                                    then
                                      let uu____10583 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____10583
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____10588 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____10590 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____10590
        then
          let uu____10591 = solve_prob orig None [] wl  in
          solve env uu____10591
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____10595 = FStar_Util.physical_equality t1 t2  in
           if uu____10595
           then
             let uu____10596 = solve_prob orig None [] wl  in
             solve env uu____10596
           else
             ((let uu____10599 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____10599
               then
                 let uu____10600 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____10600
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____10603,uu____10604) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____10605,FStar_Syntax_Syntax.Tm_bvar uu____10606) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___132_10646 =
                     match uu___132_10646 with
                     | [] -> c
                     | bs ->
                         let uu____10660 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____10660
                      in
                   let uu____10670 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____10670 with
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
                                   let uu____10756 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____10756
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____10758 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_66  ->
                                      FStar_TypeChecker_Common.CProb _0_66)
                                   uu____10758))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___133_10810 =
                     match uu___133_10810 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____10835 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____10835 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____10918 =
                                   let uu____10921 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____10922 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____10921
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____10922 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_67  ->
                                      FStar_TypeChecker_Common.TProb _0_67)
                                   uu____10918))
               | (FStar_Syntax_Syntax.Tm_abs uu____10925,uu____10926) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____10944 -> true
                     | uu____10954 -> false  in
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
                   let uu____10982 =
                     let uu____10993 = maybe_eta t1  in
                     let uu____10998 = maybe_eta t2  in
                     (uu____10993, uu____10998)  in
                   (match uu____10982 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11029 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11029.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11029.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11029.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11029.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11029.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11029.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11029.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11029.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11048 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11048
                        then
                          let uu____11049 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11049 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11070 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11070
                        then
                          let uu____11071 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11071 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11076 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11087,FStar_Syntax_Syntax.Tm_abs uu____11088) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11106 -> true
                     | uu____11116 -> false  in
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
                   let uu____11144 =
                     let uu____11155 = maybe_eta t1  in
                     let uu____11160 = maybe_eta t2  in
                     (uu____11155, uu____11160)  in
                   (match uu____11144 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11191 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11191.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11191.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11191.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11191.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11191.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11191.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11191.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11191.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11210 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11210
                        then
                          let uu____11211 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11211 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11232 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11232
                        then
                          let uu____11233 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11233 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11238 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11249,FStar_Syntax_Syntax.Tm_refine uu____11250) ->
                   let uu____11259 = as_refinement env wl t1  in
                   (match uu____11259 with
                    | (x1,phi1) ->
                        let uu____11264 = as_refinement env wl t2  in
                        (match uu____11264 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11270 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_68  ->
                                    FStar_TypeChecker_Common.TProb _0_68)
                                 uu____11270
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
                               let uu____11303 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____11303
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____11307 =
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
                                 let uu____11313 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____11313 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11320 =
                                   let uu____11323 =
                                     let uu____11324 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____11324 :: (p_scope orig)  in
                                   mk_problem uu____11323 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_69  ->
                                      FStar_TypeChecker_Common.TProb _0_69)
                                   uu____11320
                                  in
                               let uu____11327 =
                                 solve env1
                                   (let uu___167_11328 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11328.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11328.smt_ok);
                                      tcenv = (uu___167_11328.tcenv)
                                    })
                                  in
                               (match uu____11327 with
                                | Failed uu____11332 -> fallback ()
                                | Success uu____11335 ->
                                    let guard =
                                      let uu____11339 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst
                                         in
                                      let uu____11342 =
                                        let uu____11343 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst
                                           in
                                        FStar_All.pipe_right uu____11343
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____11339
                                        uu____11342
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___168_11350 = wl1  in
                                      {
                                        attempting =
                                          (uu___168_11350.attempting);
                                        wl_deferred =
                                          (uu___168_11350.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11350.defer_ok);
                                        smt_ok = (uu___168_11350.smt_ok);
                                        tcenv = (uu___168_11350.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11352,FStar_Syntax_Syntax.Tm_uvar uu____11353) ->
                   let uu____11370 = destruct_flex_t t1  in
                   let uu____11371 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11370 uu____11371
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11372;
                     FStar_Syntax_Syntax.tk = uu____11373;
                     FStar_Syntax_Syntax.pos = uu____11374;
                     FStar_Syntax_Syntax.vars = uu____11375;_},uu____11376),FStar_Syntax_Syntax.Tm_uvar
                  uu____11377) ->
                   let uu____11408 = destruct_flex_t t1  in
                   let uu____11409 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11408 uu____11409
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11410,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11411;
                     FStar_Syntax_Syntax.tk = uu____11412;
                     FStar_Syntax_Syntax.pos = uu____11413;
                     FStar_Syntax_Syntax.vars = uu____11414;_},uu____11415))
                   ->
                   let uu____11446 = destruct_flex_t t1  in
                   let uu____11447 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11446 uu____11447
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11448;
                     FStar_Syntax_Syntax.tk = uu____11449;
                     FStar_Syntax_Syntax.pos = uu____11450;
                     FStar_Syntax_Syntax.vars = uu____11451;_},uu____11452),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11453;
                     FStar_Syntax_Syntax.tk = uu____11454;
                     FStar_Syntax_Syntax.pos = uu____11455;
                     FStar_Syntax_Syntax.vars = uu____11456;_},uu____11457))
                   ->
                   let uu____11502 = destruct_flex_t t1  in
                   let uu____11503 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11502 uu____11503
               | (FStar_Syntax_Syntax.Tm_uvar uu____11504,uu____11505) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11514 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____11514 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11518;
                     FStar_Syntax_Syntax.tk = uu____11519;
                     FStar_Syntax_Syntax.pos = uu____11520;
                     FStar_Syntax_Syntax.vars = uu____11521;_},uu____11522),uu____11523)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____11546 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____11546 t2 wl
               | (uu____11550,FStar_Syntax_Syntax.Tm_uvar uu____11551) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____11560,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11561;
                     FStar_Syntax_Syntax.tk = uu____11562;
                     FStar_Syntax_Syntax.pos = uu____11563;
                     FStar_Syntax_Syntax.vars = uu____11564;_},uu____11565))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11588,FStar_Syntax_Syntax.Tm_type uu____11589) ->
                   solve_t' env
                     (let uu___169_11598 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11598.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11598.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11598.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11598.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11598.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11598.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11598.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11598.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11598.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11599;
                     FStar_Syntax_Syntax.tk = uu____11600;
                     FStar_Syntax_Syntax.pos = uu____11601;
                     FStar_Syntax_Syntax.vars = uu____11602;_},uu____11603),FStar_Syntax_Syntax.Tm_type
                  uu____11604) ->
                   solve_t' env
                     (let uu___169_11627 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11627.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11627.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11627.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11627.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11627.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11627.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11627.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11627.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11627.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11628,FStar_Syntax_Syntax.Tm_arrow uu____11629) ->
                   solve_t' env
                     (let uu___169_11645 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11645.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11645.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11645.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11645.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11645.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11645.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11645.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11645.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11645.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11646;
                     FStar_Syntax_Syntax.tk = uu____11647;
                     FStar_Syntax_Syntax.pos = uu____11648;
                     FStar_Syntax_Syntax.vars = uu____11649;_},uu____11650),FStar_Syntax_Syntax.Tm_arrow
                  uu____11651) ->
                   solve_t' env
                     (let uu___169_11681 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_11681.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_11681.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_11681.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_11681.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_11681.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_11681.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_11681.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_11681.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_11681.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____11682,uu____11683) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____11694 =
                        let uu____11695 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____11695  in
                      if uu____11694
                      then
                        let uu____11696 =
                          FStar_All.pipe_left
                            (fun _0_70  ->
                               FStar_TypeChecker_Common.TProb _0_70)
                            (let uu___170_11699 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_11699.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_11699.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_11699.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_11699.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_11699.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_11699.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_11699.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_11699.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_11699.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____11700 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____11696 uu____11700 t2
                          wl
                      else
                        (let uu____11705 = base_and_refinement env wl t2  in
                         match uu____11705 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11735 =
                                    FStar_All.pipe_left
                                      (fun _0_71  ->
                                         FStar_TypeChecker_Common.TProb _0_71)
                                      (let uu___171_11738 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_11738.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_11738.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_11738.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_11738.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_11738.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_11738.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_11738.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_11738.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_11738.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____11739 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____11735
                                    uu____11739 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_11754 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_11754.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_11754.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____11757 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_72  ->
                                         FStar_TypeChecker_Common.TProb _0_72)
                                      uu____11757
                                     in
                                  let guard =
                                    let uu____11765 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____11765
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11771;
                     FStar_Syntax_Syntax.tk = uu____11772;
                     FStar_Syntax_Syntax.pos = uu____11773;
                     FStar_Syntax_Syntax.vars = uu____11774;_},uu____11775),uu____11776)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____11801 =
                        let uu____11802 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____11802  in
                      if uu____11801
                      then
                        let uu____11803 =
                          FStar_All.pipe_left
                            (fun _0_73  ->
                               FStar_TypeChecker_Common.TProb _0_73)
                            (let uu___170_11806 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_11806.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_11806.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_11806.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_11806.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_11806.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_11806.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_11806.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_11806.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_11806.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____11807 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____11803 uu____11807 t2
                          wl
                      else
                        (let uu____11812 = base_and_refinement env wl t2  in
                         match uu____11812 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____11842 =
                                    FStar_All.pipe_left
                                      (fun _0_74  ->
                                         FStar_TypeChecker_Common.TProb _0_74)
                                      (let uu___171_11845 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_11845.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_11845.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_11845.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_11845.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_11845.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_11845.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_11845.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_11845.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_11845.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____11846 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____11842
                                    uu____11846 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___172_11861 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_11861.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_11861.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____11864 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_75  ->
                                         FStar_TypeChecker_Common.TProb _0_75)
                                      uu____11864
                                     in
                                  let guard =
                                    let uu____11872 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____11872
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____11878,FStar_Syntax_Syntax.Tm_uvar uu____11879) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11889 = base_and_refinement env wl t1  in
                      match uu____11889 with
                      | (t_base,uu____11900) ->
                          solve_t env
                            (let uu___173_11915 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_11915.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_11915.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_11915.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_11915.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_11915.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_11915.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_11915.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_11915.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____11918,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11919;
                     FStar_Syntax_Syntax.tk = uu____11920;
                     FStar_Syntax_Syntax.pos = uu____11921;
                     FStar_Syntax_Syntax.vars = uu____11922;_},uu____11923))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____11947 = base_and_refinement env wl t1  in
                      match uu____11947 with
                      | (t_base,uu____11958) ->
                          solve_t env
                            (let uu___173_11973 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_11973.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_11973.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_11973.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_11973.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_11973.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_11973.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_11973.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_11973.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____11976,uu____11977) ->
                   let t21 =
                     let uu____11985 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____11985  in
                   solve_t env
                     (let uu___174_11998 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_11998.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_11998.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_11998.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_11998.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_11998.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_11998.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_11998.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_11998.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_11998.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____11999,FStar_Syntax_Syntax.Tm_refine uu____12000) ->
                   let t11 =
                     let uu____12008 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____12008  in
                   solve_t env
                     (let uu___175_12021 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12021.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12021.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12021.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12021.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12021.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12021.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12021.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12021.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12021.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12024,uu____12025) ->
                   let head1 =
                     let uu____12044 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12044 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12075 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12075 FStar_Pervasives.fst
                      in
                   let uu____12103 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12103
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12112 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12112
                      then
                        let guard =
                          let uu____12119 =
                            let uu____12120 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12120 = FStar_Syntax_Util.Equal  in
                          if uu____12119
                          then None
                          else
                            (let uu____12123 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____12123)
                           in
                        let uu____12125 = solve_prob orig guard [] wl  in
                        solve env uu____12125
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12128,uu____12129) ->
                   let head1 =
                     let uu____12137 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12137 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12168 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12168 FStar_Pervasives.fst
                      in
                   let uu____12196 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12196
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12205 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12205
                      then
                        let guard =
                          let uu____12212 =
                            let uu____12213 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12213 = FStar_Syntax_Util.Equal  in
                          if uu____12212
                          then None
                          else
                            (let uu____12216 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____12216)
                           in
                        let uu____12218 = solve_prob orig guard [] wl  in
                        solve env uu____12218
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12221,uu____12222) ->
                   let head1 =
                     let uu____12226 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12226 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12257 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12257 FStar_Pervasives.fst
                      in
                   let uu____12285 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12285
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12294 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12294
                      then
                        let guard =
                          let uu____12301 =
                            let uu____12302 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12302 = FStar_Syntax_Util.Equal  in
                          if uu____12301
                          then None
                          else
                            (let uu____12305 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____12305)
                           in
                        let uu____12307 = solve_prob orig guard [] wl  in
                        solve env uu____12307
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12310,uu____12311) ->
                   let head1 =
                     let uu____12315 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12315 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12346 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12346 FStar_Pervasives.fst
                      in
                   let uu____12374 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12374
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12383 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12383
                      then
                        let guard =
                          let uu____12390 =
                            let uu____12391 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12391 = FStar_Syntax_Util.Equal  in
                          if uu____12390
                          then None
                          else
                            (let uu____12394 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____12394)
                           in
                        let uu____12396 = solve_prob orig guard [] wl  in
                        solve env uu____12396
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12399,uu____12400) ->
                   let head1 =
                     let uu____12404 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12404 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12435 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12435 FStar_Pervasives.fst
                      in
                   let uu____12463 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12463
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12472 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12472
                      then
                        let guard =
                          let uu____12479 =
                            let uu____12480 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12480 = FStar_Syntax_Util.Equal  in
                          if uu____12479
                          then None
                          else
                            (let uu____12483 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____12483)
                           in
                        let uu____12485 = solve_prob orig guard [] wl  in
                        solve env uu____12485
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____12488,uu____12489) ->
                   let head1 =
                     let uu____12502 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12502 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12533 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12533 FStar_Pervasives.fst
                      in
                   let uu____12561 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12561
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12570 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12570
                      then
                        let guard =
                          let uu____12577 =
                            let uu____12578 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12578 = FStar_Syntax_Util.Equal  in
                          if uu____12577
                          then None
                          else
                            (let uu____12581 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____12581)
                           in
                        let uu____12583 = solve_prob orig guard [] wl  in
                        solve env uu____12583
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12586,FStar_Syntax_Syntax.Tm_match uu____12587) ->
                   let head1 =
                     let uu____12606 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12606 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12637 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12637 FStar_Pervasives.fst
                      in
                   let uu____12665 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12665
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12674 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12674
                      then
                        let guard =
                          let uu____12681 =
                            let uu____12682 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12682 = FStar_Syntax_Util.Equal  in
                          if uu____12681
                          then None
                          else
                            (let uu____12685 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____12685)
                           in
                        let uu____12687 = solve_prob orig guard [] wl  in
                        solve env uu____12687
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12690,FStar_Syntax_Syntax.Tm_uinst uu____12691) ->
                   let head1 =
                     let uu____12699 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12699 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12730 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12730 FStar_Pervasives.fst
                      in
                   let uu____12758 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12758
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12767 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12767
                      then
                        let guard =
                          let uu____12774 =
                            let uu____12775 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12775 = FStar_Syntax_Util.Equal  in
                          if uu____12774
                          then None
                          else
                            (let uu____12778 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_83  -> Some _0_83)
                               uu____12778)
                           in
                        let uu____12780 = solve_prob orig guard [] wl  in
                        solve env uu____12780
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12783,FStar_Syntax_Syntax.Tm_name uu____12784) ->
                   let head1 =
                     let uu____12788 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12788 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12819 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12819 FStar_Pervasives.fst
                      in
                   let uu____12847 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12847
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12856 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12856
                      then
                        let guard =
                          let uu____12863 =
                            let uu____12864 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12864 = FStar_Syntax_Util.Equal  in
                          if uu____12863
                          then None
                          else
                            (let uu____12867 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_84  -> Some _0_84)
                               uu____12867)
                           in
                        let uu____12869 = solve_prob orig guard [] wl  in
                        solve env uu____12869
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12872,FStar_Syntax_Syntax.Tm_constant uu____12873) ->
                   let head1 =
                     let uu____12877 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12877 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12908 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12908 FStar_Pervasives.fst
                      in
                   let uu____12936 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12936
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12945 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12945
                      then
                        let guard =
                          let uu____12952 =
                            let uu____12953 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12953 = FStar_Syntax_Util.Equal  in
                          if uu____12952
                          then None
                          else
                            (let uu____12956 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                               uu____12956)
                           in
                        let uu____12958 = solve_prob orig guard [] wl  in
                        solve env uu____12958
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____12961,FStar_Syntax_Syntax.Tm_fvar uu____12962) ->
                   let head1 =
                     let uu____12966 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12966 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12997 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12997 FStar_Pervasives.fst
                      in
                   let uu____13025 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13025
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13034 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13034
                      then
                        let guard =
                          let uu____13041 =
                            let uu____13042 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13042 = FStar_Syntax_Util.Equal  in
                          if uu____13041
                          then None
                          else
                            (let uu____13045 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_86  -> Some _0_86)
                               uu____13045)
                           in
                        let uu____13047 = solve_prob orig guard [] wl  in
                        solve env uu____13047
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13050,FStar_Syntax_Syntax.Tm_app uu____13051) ->
                   let head1 =
                     let uu____13064 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13064 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13095 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13095 FStar_Pervasives.fst
                      in
                   let uu____13123 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13123
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13132 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13132
                      then
                        let guard =
                          let uu____13139 =
                            let uu____13140 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13140 = FStar_Syntax_Util.Equal  in
                          if uu____13139
                          then None
                          else
                            (let uu____13143 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_87  -> Some _0_87)
                               uu____13143)
                           in
                        let uu____13145 = solve_prob orig guard [] wl  in
                        solve env uu____13145
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13149,uu____13150),uu____13151) ->
                   solve_t' env
                     (let uu___176_13180 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___176_13180.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___176_13180.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___176_13180.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___176_13180.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___176_13180.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___176_13180.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___176_13180.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___176_13180.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___176_13180.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13183,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13185,uu____13186)) ->
                   solve_t' env
                     (let uu___177_13215 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___177_13215.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___177_13215.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___177_13215.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___177_13215.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___177_13215.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___177_13215.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___177_13215.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___177_13215.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___177_13215.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13216,uu____13217) ->
                   let uu____13225 =
                     let uu____13226 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13227 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13226
                       uu____13227
                      in
                   failwith uu____13225
               | (FStar_Syntax_Syntax.Tm_meta uu____13228,uu____13229) ->
                   let uu____13234 =
                     let uu____13235 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13236 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13235
                       uu____13236
                      in
                   failwith uu____13234
               | (FStar_Syntax_Syntax.Tm_delayed uu____13237,uu____13238) ->
                   let uu____13253 =
                     let uu____13254 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13255 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13254
                       uu____13255
                      in
                   failwith uu____13253
               | (uu____13256,FStar_Syntax_Syntax.Tm_meta uu____13257) ->
                   let uu____13262 =
                     let uu____13263 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13264 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13263
                       uu____13264
                      in
                   failwith uu____13262
               | (uu____13265,FStar_Syntax_Syntax.Tm_delayed uu____13266) ->
                   let uu____13281 =
                     let uu____13282 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13283 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13282
                       uu____13283
                      in
                   failwith uu____13281
               | (uu____13284,FStar_Syntax_Syntax.Tm_let uu____13285) ->
                   let uu____13293 =
                     let uu____13294 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13295 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13294
                       uu____13295
                      in
                   failwith uu____13293
               | uu____13296 -> giveup env "head tag mismatch" orig)))

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
          (let uu____13328 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____13328
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13336  ->
                  fun uu____13337  ->
                    match (uu____13336, uu____13337) with
                    | ((a1,uu____13347),(a2,uu____13349)) ->
                        let uu____13354 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_88  -> FStar_TypeChecker_Common.TProb _0_88)
                          uu____13354)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____13360 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____13360  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____13380 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13387)::[] -> wp1
              | uu____13400 ->
                  let uu____13406 =
                    let uu____13407 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13407
                     in
                  failwith uu____13406
               in
            let uu____13410 =
              let uu____13416 =
                let uu____13417 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____13417  in
              [uu____13416]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13410;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13418 = lift_c1 ()  in solve_eq uu____13418 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___134_13422  ->
                       match uu___134_13422 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13423 -> false))
                in
             let uu____13424 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13448)::uu____13449,(wp2,uu____13451)::uu____13452)
                   -> (wp1, wp2)
               | uu____13493 ->
                   let uu____13506 =
                     let uu____13507 =
                       let uu____13510 =
                         let uu____13511 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____13512 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____13511 uu____13512
                          in
                       (uu____13510, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____13507  in
                   raise uu____13506
                in
             match uu____13424 with
             | (wpc1,wpc2) ->
                 let uu____13529 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____13529
                 then
                   let uu____13532 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type"
                      in
                   solve_t env uu____13532 wl
                 else
                   (let uu____13536 =
                      let uu____13540 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____13540  in
                    match uu____13536 with
                    | (c2_decl,qualifiers) ->
                        let uu____13552 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____13552
                        then
                          let c1_repr =
                            let uu____13555 =
                              let uu____13556 =
                                let uu____13557 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____13557  in
                              let uu____13558 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13556 uu____13558
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13555
                             in
                          let c2_repr =
                            let uu____13560 =
                              let uu____13561 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____13562 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____13561 uu____13562
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____13560
                             in
                          let prob =
                            let uu____13564 =
                              let uu____13567 =
                                let uu____13568 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____13569 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____13568
                                  uu____13569
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____13567
                               in
                            FStar_TypeChecker_Common.TProb uu____13564  in
                          let wl1 =
                            let uu____13571 =
                              let uu____13573 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst
                                 in
                              Some uu____13573  in
                            solve_prob orig uu____13571 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____13580 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____13580
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____13582 =
                                     let uu____13585 =
                                       let uu____13586 =
                                         let uu____13596 =
                                           let uu____13597 =
                                             let uu____13598 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ
                                                in
                                             [uu____13598]  in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____13597 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____13599 =
                                           let uu____13601 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____13602 =
                                             let uu____13604 =
                                               let uu____13605 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____13605
                                                in
                                             [uu____13604]  in
                                           uu____13601 :: uu____13602  in
                                         (uu____13596, uu____13599)  in
                                       FStar_Syntax_Syntax.Tm_app uu____13586
                                        in
                                     FStar_Syntax_Syntax.mk uu____13585  in
                                   uu____13582
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____13616 =
                                    let uu____13619 =
                                      let uu____13620 =
                                        let uu____13630 =
                                          let uu____13631 =
                                            let uu____13632 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____13632]  in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____13631 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____13633 =
                                          let uu____13635 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____13636 =
                                            let uu____13638 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____13639 =
                                              let uu____13641 =
                                                let uu____13642 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____13642
                                                 in
                                              [uu____13641]  in
                                            uu____13638 :: uu____13639  in
                                          uu____13635 :: uu____13636  in
                                        (uu____13630, uu____13633)  in
                                      FStar_Syntax_Syntax.Tm_app uu____13620
                                       in
                                    FStar_Syntax_Syntax.mk uu____13619  in
                                  uu____13616
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r)
                              in
                           let base_prob =
                             let uu____13653 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_89  ->
                                  FStar_TypeChecker_Common.TProb _0_89)
                               uu____13653
                              in
                           let wl1 =
                             let uu____13659 =
                               let uu____13661 =
                                 let uu____13664 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____13664 g  in
                               FStar_All.pipe_left (fun _0_90  -> Some _0_90)
                                 uu____13661
                                in
                             solve_prob orig uu____13659 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____13674 = FStar_Util.physical_equality c1 c2  in
        if uu____13674
        then
          let uu____13675 = solve_prob orig None [] wl  in
          solve env uu____13675
        else
          ((let uu____13678 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____13678
            then
              let uu____13679 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____13680 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____13679
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____13680
            else ());
           (let uu____13682 =
              let uu____13685 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____13686 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____13685, uu____13686)  in
            match uu____13682 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13690),FStar_Syntax_Syntax.Total
                    (t2,uu____13692)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____13705 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____13705 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____13708,FStar_Syntax_Syntax.Total uu____13709) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____13721),FStar_Syntax_Syntax.Total
                    (t2,uu____13723)) ->
                     let uu____13736 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____13736 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____13740),FStar_Syntax_Syntax.GTotal
                    (t2,uu____13742)) ->
                     let uu____13755 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____13755 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____13759),FStar_Syntax_Syntax.GTotal
                    (t2,uu____13761)) ->
                     let uu____13774 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____13774 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____13777,FStar_Syntax_Syntax.Comp uu____13778) ->
                     let uu____13784 =
                       let uu___178_13787 = problem  in
                       let uu____13790 =
                         let uu____13791 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13791
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_13787.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____13790;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_13787.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_13787.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_13787.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_13787.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_13787.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_13787.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_13787.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_13787.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____13784 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____13792,FStar_Syntax_Syntax.Comp uu____13793) ->
                     let uu____13799 =
                       let uu___178_13802 = problem  in
                       let uu____13805 =
                         let uu____13806 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13806
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___178_13802.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____13805;
                         FStar_TypeChecker_Common.relation =
                           (uu___178_13802.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___178_13802.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___178_13802.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___178_13802.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___178_13802.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___178_13802.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___178_13802.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___178_13802.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____13799 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13807,FStar_Syntax_Syntax.GTotal uu____13808) ->
                     let uu____13814 =
                       let uu___179_13817 = problem  in
                       let uu____13820 =
                         let uu____13821 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13821
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_13817.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_13817.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_13817.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____13820;
                         FStar_TypeChecker_Common.element =
                           (uu___179_13817.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_13817.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_13817.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_13817.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_13817.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_13817.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____13814 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13822,FStar_Syntax_Syntax.Total uu____13823) ->
                     let uu____13829 =
                       let uu___179_13832 = problem  in
                       let uu____13835 =
                         let uu____13836 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____13836
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___179_13832.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___179_13832.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___179_13832.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____13835;
                         FStar_TypeChecker_Common.element =
                           (uu___179_13832.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___179_13832.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___179_13832.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___179_13832.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___179_13832.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___179_13832.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____13829 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____13837,FStar_Syntax_Syntax.Comp uu____13838) ->
                     let uu____13839 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____13839
                     then
                       let uu____13840 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type"
                          in
                       solve_t env uu____13840 wl
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
                           (let uu____13850 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____13850
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____13852 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____13852 with
                            | None  ->
                                let uu____13854 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____13855 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____13855)
                                   in
                                if uu____13854
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
                                  (let uu____13858 =
                                     let uu____13859 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____13860 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____13859 uu____13860
                                      in
                                   giveup env uu____13858 orig)
                            | Some edge -> solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____13865 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____13881  ->
              match uu____13881 with
              | (uu____13888,uu____13889,u,uu____13891,uu____13892,uu____13893)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____13865 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____13911 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____13911 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____13921 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____13933  ->
                match uu____13933 with
                | (u1,u2) ->
                    let uu____13938 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____13939 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____13938 uu____13939))
         in
      FStar_All.pipe_right uu____13921 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____13951,[])) -> "{}"
      | uu____13964 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____13974 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____13974
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____13977 =
              FStar_List.map
                (fun uu____13981  ->
                   match uu____13981 with
                   | (uu____13984,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____13977 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____13988 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____13988 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14026 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____14026
    then
      let uu____14027 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____14028 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14027
        (rel_to_string rel) uu____14028
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
            let uu____14048 =
              let uu____14050 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_91  -> Some _0_91) uu____14050  in
            FStar_Syntax_Syntax.new_bv uu____14048 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____14056 =
              let uu____14058 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_92  -> Some _0_92) uu____14058  in
            let uu____14060 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____14056 uu____14060  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob * Prims.string) ->
         FStar_TypeChecker_Common.deferred option)
        -> FStar_TypeChecker_Common.deferred option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____14083 = FStar_Options.eager_inference ()  in
          if uu____14083
          then
            let uu___180_14084 = probs  in
            {
              attempting = (uu___180_14084.attempting);
              wl_deferred = (uu___180_14084.wl_deferred);
              ctr = (uu___180_14084.ctr);
              defer_ok = false;
              smt_ok = (uu___180_14084.smt_ok);
              tcenv = (uu___180_14084.tcenv)
            }
          else probs  in
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Syntax_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Syntax_Unionfind.rollback tx;
             (let uu____14095 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____14095
              then
                let uu____14096 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____14096
              else ());
             err1 (d, s))
  
let simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____14106 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____14106
            then
              let uu____14107 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14107
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify;
                FStar_TypeChecker_Normalize.Primops] env f
               in
            (let uu____14111 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____14111
             then
               let uu____14112 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14112
             else ());
            (let f2 =
               let uu____14115 =
                 let uu____14116 = FStar_Syntax_Util.unmeta f1  in
                 uu____14116.FStar_Syntax_Syntax.n  in
               match uu____14115 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14120 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___181_14121 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___181_14121.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_14121.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_14121.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_TypeChecker_Common.deferred option ->
        FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | None  -> None
        | Some d ->
            let uu____14136 =
              let uu____14137 =
                let uu____14138 =
                  let uu____14139 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst
                     in
                  FStar_All.pipe_right uu____14139
                    (fun _0_93  -> FStar_TypeChecker_Common.NonTrivial _0_93)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14138;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____14137  in
            FStar_All.pipe_left (fun _0_94  -> Some _0_94) uu____14136
  
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14172 =
        let uu____14173 =
          let uu____14174 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst  in
          FStar_All.pipe_right uu____14174
            (fun _0_95  -> FStar_TypeChecker_Common.NonTrivial _0_95)
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____14173;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        }  in
      Some uu____14172
  
let try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____14200 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14200
           then
             let uu____14201 = FStar_Syntax_Print.term_to_string t1  in
             let uu____14202 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14201
               uu____14202
           else ());
          (let prob =
             let uu____14205 =
               let uu____14208 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14208
                in
             FStar_All.pipe_left
               (fun _0_96  -> FStar_TypeChecker_Common.TProb _0_96)
               uu____14205
              in
           let g =
             let uu____14213 =
               let uu____14215 = singleton' env prob smt_ok  in
               solve_and_commit env uu____14215 (fun uu____14216  -> None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____14213  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14230 = try_teq true env t1 t2  in
        match uu____14230 with
        | None  ->
            let uu____14232 =
              let uu____14233 =
                let uu____14236 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____14237 = FStar_TypeChecker_Env.get_range env  in
                (uu____14236, uu____14237)  in
              FStar_Errors.Error uu____14233  in
            raise uu____14232
        | Some g ->
            ((let uu____14240 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____14240
              then
                let uu____14241 = FStar_Syntax_Print.term_to_string t1  in
                let uu____14242 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14243 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14241
                  uu____14242 uu____14243
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14259 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14259
           then
             let uu____14260 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____14261 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14260
               uu____14261
           else ());
          (let uu____14263 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____14263 with
           | (prob,x) ->
               let g =
                 let uu____14271 =
                   let uu____14273 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____14273
                     (fun uu____14274  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____14271  in
               ((let uu____14280 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____14280
                 then
                   let uu____14281 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____14282 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____14283 =
                     let uu____14284 = FStar_Util.must g  in
                     guard_to_string env uu____14284  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14281 uu____14282 uu____14283
                 else ());
                abstract_guard x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t option
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
          let uu____14308 = FStar_TypeChecker_Env.get_range env  in
          let uu____14309 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.err uu____14308 uu____14309
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14321 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____14321
         then
           let uu____14322 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____14323 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14322
             uu____14323
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____14328 =
             let uu____14331 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____14331 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_97  -> FStar_TypeChecker_Common.CProb _0_97) uu____14328
            in
         let uu____14334 =
           let uu____14336 = singleton env prob  in
           solve_and_commit env uu____14336 (fun uu____14337  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____14334)
  
let solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14356  ->
        match uu____14356 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____14381 =
                 let uu____14382 =
                   let uu____14385 =
                     let uu____14386 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____14387 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14386 uu____14387
                      in
                   let uu____14388 = FStar_TypeChecker_Env.get_range env  in
                   (uu____14385, uu____14388)  in
                 FStar_Errors.Error uu____14382  in
               raise uu____14381)
               in
            let equiv1 v1 v' =
              let uu____14396 =
                let uu____14399 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____14400 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____14399, uu____14400)  in
              match uu____14396 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____14407 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14421 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____14421 with
                      | FStar_Syntax_Syntax.U_unif uu____14425 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14436  ->
                                    match uu____14436 with
                                    | (u,v') ->
                                        let uu____14442 = equiv1 v1 v'  in
                                        if uu____14442
                                        then
                                          let uu____14444 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____14444 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____14454 -> []))
               in
            let uu____14457 =
              let wl =
                let uu___182_14460 = empty_worklist env  in
                {
                  attempting = (uu___182_14460.attempting);
                  wl_deferred = (uu___182_14460.wl_deferred);
                  ctr = (uu___182_14460.ctr);
                  defer_ok = false;
                  smt_ok = (uu___182_14460.smt_ok);
                  tcenv = (uu___182_14460.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____14467  ->
                      match uu____14467 with
                      | (lb,v1) ->
                          let uu____14472 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____14472 with
                           | USolved wl1 -> ()
                           | uu____14474 -> fail lb v1)))
               in
            let rec check_ineq uu____14480 =
              match uu____14480 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____14487) -> true
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
                      uu____14498,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____14500,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____14505) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____14509,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____14514 -> false)
               in
            let uu____14517 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____14523  ->
                      match uu____14523 with
                      | (u,v1) ->
                          let uu____14528 = check_ineq (u, v1)  in
                          if uu____14528
                          then true
                          else
                            ((let uu____14531 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____14531
                              then
                                let uu____14532 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____14533 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____14532
                                  uu____14533
                              else ());
                             false)))
               in
            if uu____14517
            then ()
            else
              ((let uu____14537 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____14537
                then
                  ((let uu____14539 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____14539);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____14545 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____14545))
                else ());
               (let uu____14551 =
                  let uu____14552 =
                    let uu____14555 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____14555)
                     in
                  FStar_Errors.Error uu____14552  in
                raise uu____14551))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> Prims.unit
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let rec solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let fail uu____14588 =
        match uu____14588 with
        | (d,s) ->
            let msg = explain env d s  in
            raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____14598 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____14598
       then
         let uu____14599 = wl_to_string wl  in
         let uu____14600 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____14599 uu____14600
       else ());
      (let g1 =
         let uu____14612 = solve_and_commit env wl fail  in
         match uu____14612 with
         | Some [] ->
             let uu___183_14619 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___183_14619.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___183_14619.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___183_14619.FStar_TypeChecker_Env.implicits)
             }
         | uu____14622 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___184_14625 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___184_14625.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___184_14625.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___184_14625.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool -> FStar_TypeChecker_Env.guard_t option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___185_14651 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___185_14651.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___185_14651.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___185_14651.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____14652 =
            let uu____14653 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____14653  in
          if uu____14652
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____14659 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery"))
                      in
                   if uu____14659
                   then
                     let uu____14660 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____14661 =
                       let uu____14662 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____14662
                        in
                     FStar_Errors.diag uu____14660 uu____14661
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Simplify;
                       FStar_TypeChecker_Normalize.Primops] env vc
                      in
                   let uu____14665 = check_trivial vc1  in
                   match uu____14665 with
                   | FStar_TypeChecker_Common.Trivial  -> Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then
                         ((let uu____14670 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____14670
                           then
                             let uu____14671 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____14672 =
                               let uu____14673 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1
                                 "Cannot solve without SMT : %s\n"
                                 uu____14673
                                in
                             FStar_Errors.diag uu____14671 uu____14672
                           else ());
                          None)
                       else
                         ((let uu____14678 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____14678
                           then
                             let uu____14679 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____14680 =
                               let uu____14681 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____14681
                                in
                             FStar_Errors.diag uu____14679 uu____14680
                           else ());
                          (let vcs =
                             let uu____14688 = FStar_Options.use_tactics ()
                                in
                             if uu____14688
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else
                               (let uu____14694 =
                                  let uu____14698 = FStar_Options.peek ()  in
                                  (env, vc2, uu____14698)  in
                                [uu____14694])
                              in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____14712  ->
                                   match uu____14712 with
                                   | (env1,goal,opts) ->
                                       let goal1 =
                                         FStar_TypeChecker_Normalize.normalize
                                           [FStar_TypeChecker_Normalize.Simplify;
                                           FStar_TypeChecker_Normalize.Primops]
                                           env1 goal
                                          in
                                       let uu____14720 = check_trivial goal1
                                          in
                                       (match uu____14720 with
                                        | FStar_TypeChecker_Common.Trivial 
                                            ->
                                            let uu____14722 =
                                              (FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other "Rel"))
                                                ||
                                                (FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other "Tac"))
                                               in
                                            if uu____14722
                                            then
                                              FStar_Util.print_string
                                                "Goal completely solved by tactic\n"
                                            else ()
                                        | FStar_TypeChecker_Common.NonTrivial
                                            goal2 ->
                                            (FStar_Options.push ();
                                             FStar_Options.set opts;
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                                               ();
                                             (let uu____14729 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other "Rel")
                                                 in
                                              if uu____14729
                                              then
                                                let uu____14730 =
                                                  FStar_TypeChecker_Env.get_range
                                                    env1
                                                   in
                                                let uu____14731 =
                                                  let uu____14732 =
                                                    FStar_Syntax_Print.term_to_string
                                                      goal2
                                                     in
                                                  let uu____14733 =
                                                    FStar_TypeChecker_Env.string_of_proof_ns
                                                      env1
                                                     in
                                                  FStar_Util.format2
                                                    "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                    uu____14732 uu____14733
                                                   in
                                                FStar_Errors.diag uu____14730
                                                  uu____14731
                                              else ());
                                             (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                               use_env_range_msg env1 goal2;
                                             FStar_Options.pop ())))));
                          Some ret_g))))
  
let discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____14743 = discharge_guard' None env g false  in
      match uu____14743 with
      | Some g1 -> g1
      | None  ->
          let uu____14748 =
            let uu____14749 =
              let uu____14752 = FStar_TypeChecker_Env.get_range env  in
              ("Expected a trivial pre-condition", uu____14752)  in
            FStar_Errors.Error uu____14749  in
          raise uu____14748
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____14759 = discharge_guard' None env g true  in
      match uu____14759 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits' :
  Prims.bool ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun forcelax  ->
    fun g  ->
      let unresolved u =
        let uu____14774 = FStar_Syntax_Unionfind.find u  in
        match uu____14774 with | None  -> true | uu____14776 -> false  in
      let rec until_fixpoint acc implicits =
        let uu____14789 = acc  in
        match uu____14789 with
        | (out,changed) ->
            (match implicits with
             | [] ->
                 if Prims.op_Negation changed
                 then out
                 else until_fixpoint ([], false) out
             | hd1::tl1 ->
                 let uu____14835 = hd1  in
                 (match uu____14835 with
                  | (uu____14842,env,u,tm,k,r) ->
                      let uu____14848 = unresolved u  in
                      if uu____14848
                      then until_fixpoint ((hd1 :: out), changed) tl1
                      else
                        (let env1 =
                           FStar_TypeChecker_Env.set_expected_typ env k  in
                         let tm1 =
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta] env1 tm
                            in
                         (let uu____14866 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env1)
                              (FStar_Options.Other "RelCheck")
                             in
                          if uu____14866
                          then
                            let uu____14867 =
                              FStar_Syntax_Print.uvar_to_string u  in
                            let uu____14868 =
                              FStar_Syntax_Print.term_to_string tm1  in
                            let uu____14869 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print3
                              "Checking uvar %s resolved to %s at type %s\n"
                              uu____14867 uu____14868 uu____14869
                          else ());
                         (let env2 =
                            if forcelax
                            then
                              let uu___186_14872 = env1  in
                              {
                                FStar_TypeChecker_Env.solver =
                                  (uu___186_14872.FStar_TypeChecker_Env.solver);
                                FStar_TypeChecker_Env.range =
                                  (uu___186_14872.FStar_TypeChecker_Env.range);
                                FStar_TypeChecker_Env.curmodule =
                                  (uu___186_14872.FStar_TypeChecker_Env.curmodule);
                                FStar_TypeChecker_Env.gamma =
                                  (uu___186_14872.FStar_TypeChecker_Env.gamma);
                                FStar_TypeChecker_Env.gamma_cache =
                                  (uu___186_14872.FStar_TypeChecker_Env.gamma_cache);
                                FStar_TypeChecker_Env.modules =
                                  (uu___186_14872.FStar_TypeChecker_Env.modules);
                                FStar_TypeChecker_Env.expected_typ =
                                  (uu___186_14872.FStar_TypeChecker_Env.expected_typ);
                                FStar_TypeChecker_Env.sigtab =
                                  (uu___186_14872.FStar_TypeChecker_Env.sigtab);
                                FStar_TypeChecker_Env.is_pattern =
                                  (uu___186_14872.FStar_TypeChecker_Env.is_pattern);
                                FStar_TypeChecker_Env.instantiate_imp =
                                  (uu___186_14872.FStar_TypeChecker_Env.instantiate_imp);
                                FStar_TypeChecker_Env.effects =
                                  (uu___186_14872.FStar_TypeChecker_Env.effects);
                                FStar_TypeChecker_Env.generalize =
                                  (uu___186_14872.FStar_TypeChecker_Env.generalize);
                                FStar_TypeChecker_Env.letrecs =
                                  (uu___186_14872.FStar_TypeChecker_Env.letrecs);
                                FStar_TypeChecker_Env.top_level =
                                  (uu___186_14872.FStar_TypeChecker_Env.top_level);
                                FStar_TypeChecker_Env.check_uvars =
                                  (uu___186_14872.FStar_TypeChecker_Env.check_uvars);
                                FStar_TypeChecker_Env.use_eq =
                                  (uu___186_14872.FStar_TypeChecker_Env.use_eq);
                                FStar_TypeChecker_Env.is_iface =
                                  (uu___186_14872.FStar_TypeChecker_Env.is_iface);
                                FStar_TypeChecker_Env.admit =
                                  (uu___186_14872.FStar_TypeChecker_Env.admit);
                                FStar_TypeChecker_Env.lax = true;
                                FStar_TypeChecker_Env.lax_universes =
                                  (uu___186_14872.FStar_TypeChecker_Env.lax_universes);
                                FStar_TypeChecker_Env.type_of =
                                  (uu___186_14872.FStar_TypeChecker_Env.type_of);
                                FStar_TypeChecker_Env.universe_of =
                                  (uu___186_14872.FStar_TypeChecker_Env.universe_of);
                                FStar_TypeChecker_Env.use_bv_sorts =
                                  (uu___186_14872.FStar_TypeChecker_Env.use_bv_sorts);
                                FStar_TypeChecker_Env.qname_and_index =
                                  (uu___186_14872.FStar_TypeChecker_Env.qname_and_index);
                                FStar_TypeChecker_Env.proof_ns =
                                  (uu___186_14872.FStar_TypeChecker_Env.proof_ns);
                                FStar_TypeChecker_Env.synth =
                                  (uu___186_14872.FStar_TypeChecker_Env.synth);
                                FStar_TypeChecker_Env.is_native_tactic =
                                  (uu___186_14872.FStar_TypeChecker_Env.is_native_tactic)
                              }
                            else env1  in
                          let uu____14874 =
                            env2.FStar_TypeChecker_Env.type_of
                              (let uu___187_14878 = env2  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___187_14878.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___187_14878.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___187_14878.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___187_14878.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___187_14878.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___187_14878.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___187_14878.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___187_14878.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___187_14878.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___187_14878.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___187_14878.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___187_14878.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___187_14878.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___187_14878.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___187_14878.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___187_14878.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___187_14878.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___187_14878.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___187_14878.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___187_14878.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___187_14878.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___187_14878.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.use_bv_sorts = true;
                                 FStar_TypeChecker_Env.qname_and_index =
                                   (uu___187_14878.FStar_TypeChecker_Env.qname_and_index);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___187_14878.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth =
                                   (uu___187_14878.FStar_TypeChecker_Env.synth);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___187_14878.FStar_TypeChecker_Env.is_native_tactic)
                               }) tm1
                             in
                          match uu____14874 with
                          | (uu____14879,uu____14880,g1) ->
                              let g2 =
                                if env2.FStar_TypeChecker_Env.is_pattern
                                then
                                  let uu___188_14883 = g1  in
                                  {
                                    FStar_TypeChecker_Env.guard_f =
                                      FStar_TypeChecker_Common.Trivial;
                                    FStar_TypeChecker_Env.deferred =
                                      (uu___188_14883.FStar_TypeChecker_Env.deferred);
                                    FStar_TypeChecker_Env.univ_ineqs =
                                      (uu___188_14883.FStar_TypeChecker_Env.univ_ineqs);
                                    FStar_TypeChecker_Env.implicits =
                                      (uu___188_14883.FStar_TypeChecker_Env.implicits)
                                  }
                                else g1  in
                              let g' =
                                let uu____14886 =
                                  discharge_guard'
                                    (Some
                                       (fun uu____14890  ->
                                          FStar_Syntax_Print.term_to_string
                                            tm1)) env2 g2 true
                                   in
                                match uu____14886 with
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
      let uu___189_14905 = g  in
      let uu____14906 =
        until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___189_14905.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___189_14905.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs =
          (uu___189_14905.FStar_TypeChecker_Env.univ_ineqs);
        FStar_TypeChecker_Env.implicits = uu____14906
      }
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' false g 
let resolve_implicits_lax :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  -> resolve_implicits' true g 
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____14940 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____14940 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____14947 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____14947
      | (reason,uu____14949,uu____14950,e,t,r)::uu____14954 ->
          let uu____14968 =
            let uu____14969 = FStar_Syntax_Print.term_to_string t  in
            let uu____14970 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____14969 uu____14970
             in
          FStar_Errors.err r uu____14968
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___190_14977 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___190_14977.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___190_14977.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___190_14977.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14995 = try_teq false env t1 t2  in
        match uu____14995 with
        | None  -> false
        | Some g ->
            let uu____14998 = discharge_guard' None env g false  in
            (match uu____14998 with
             | Some uu____15002 -> true
             | None  -> false)
  