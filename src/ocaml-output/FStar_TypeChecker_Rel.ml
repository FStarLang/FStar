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
    FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun x  ->
    fun g  ->
      match g with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some
          {
            FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial ;
            FStar_TypeChecker_Env.deferred = uu____56;
            FStar_TypeChecker_Env.univ_ineqs = uu____57;
            FStar_TypeChecker_Env.implicits = uu____58;_}
          -> g
      | FStar_Pervasives_Native.Some g1 ->
          let f =
            match g1.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.NonTrivial f -> f
            | uu____73 -> failwith "impossible"  in
          let uu____74 =
            let uu___133_75 = g1  in
            let uu____76 =
              let uu____77 =
                let uu____78 =
                  let uu____79 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____79]  in
                let uu____80 =
                  let uu____87 =
                    let uu____93 =
                      let uu____94 =
                        FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                         in
                      FStar_All.pipe_right uu____94
                        FStar_Syntax_Util.lcomp_of_comp
                       in
                    FStar_All.pipe_right uu____93
                      (fun _0_29  -> FStar_Util.Inl _0_29)
                     in
                  FStar_Pervasives_Native.Some uu____87  in
                FStar_Syntax_Util.abs uu____78 f uu____80  in
              FStar_All.pipe_left
                (fun _0_30  -> FStar_TypeChecker_Common.NonTrivial _0_30)
                uu____77
               in
            {
              FStar_TypeChecker_Env.guard_f = uu____76;
              FStar_TypeChecker_Env.deferred =
                (uu___133_75.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___133_75.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___133_75.FStar_TypeChecker_Env.implicits)
            }  in
          FStar_Pervasives_Native.Some uu____74
  
let apply_guard :
  FStar_TypeChecker_Env.guard_t ->
    FStar_Syntax_Syntax.term -> FStar_TypeChecker_Env.guard_t
  =
  fun g  ->
    fun e  ->
      match g.FStar_TypeChecker_Env.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          let uu___134_115 = g  in
          let uu____116 =
            let uu____117 =
              let uu____118 =
                let uu____121 =
                  let uu____122 =
                    let uu____132 =
                      let uu____134 = FStar_Syntax_Syntax.as_arg e  in
                      [uu____134]  in
                    (f, uu____132)  in
                  FStar_Syntax_Syntax.Tm_app uu____122  in
                FStar_Syntax_Syntax.mk uu____121  in
              uu____118
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                f.FStar_Syntax_Syntax.pos
               in
            FStar_All.pipe_left
              (fun _0_31  -> FStar_TypeChecker_Common.NonTrivial _0_31)
              uu____117
             in
          {
            FStar_TypeChecker_Env.guard_f = uu____116;
            FStar_TypeChecker_Env.deferred =
              (uu___134_115.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___134_115.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___134_115.FStar_TypeChecker_Env.implicits)
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
          let uu___135_156 = g  in
          let uu____157 =
            let uu____158 = map1 f  in
            FStar_TypeChecker_Common.NonTrivial uu____158  in
          {
            FStar_TypeChecker_Env.guard_f = uu____157;
            FStar_TypeChecker_Env.deferred =
              (uu___135_156.FStar_TypeChecker_Env.deferred);
            FStar_TypeChecker_Env.univ_ineqs =
              (uu___135_156.FStar_TypeChecker_Env.univ_ineqs);
            FStar_TypeChecker_Env.implicits =
              (uu___135_156.FStar_TypeChecker_Env.implicits)
          }
  
let trivial : FStar_TypeChecker_Common.guard_formula -> Prims.unit =
  fun t  ->
    match t with
    | FStar_TypeChecker_Common.Trivial  -> ()
    | FStar_TypeChecker_Common.NonTrivial uu____162 -> failwith "impossible"
  
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
          let uu____173 = FStar_Syntax_Util.mk_conj f1 f2  in
          FStar_TypeChecker_Common.NonTrivial uu____173
  
let check_trivial :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_TypeChecker_Common.guard_formula
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar tc when
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Parser_Const.true_lid ->
        FStar_TypeChecker_Common.Trivial
    | uu____182 -> FStar_TypeChecker_Common.NonTrivial t
  
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
        let uu____213 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____213;
          FStar_TypeChecker_Env.deferred =
            (FStar_List.append g1.FStar_TypeChecker_Env.deferred
               g2.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs =
            ((FStar_List.append
                (FStar_Pervasives_Native.fst
                   g1.FStar_TypeChecker_Env.univ_ineqs)
                (FStar_Pervasives_Native.fst
                   g2.FStar_TypeChecker_Env.univ_ineqs)),
              (FStar_List.append
                 (FStar_Pervasives_Native.snd
                    g1.FStar_TypeChecker_Env.univ_ineqs)
                 (FStar_Pervasives_Native.snd
                    g2.FStar_TypeChecker_Env.univ_ineqs)));
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
                       let uu____258 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____258
                       then f1
                       else
                         FStar_Syntax_Util.mk_forall u
                           (FStar_Pervasives_Native.fst b) f1) us bs f
               in
            let uu___136_260 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_260.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_260.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_260.FStar_TypeChecker_Env.implicits)
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
               let uu____274 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____274
               then f1
               else
                 (let u =
                    env.FStar_TypeChecker_Env.universe_of env
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  FStar_Syntax_Util.mk_forall u
                    (FStar_Pervasives_Native.fst b) f1)) bs f
  
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
            let uu___137_287 = g  in
            let uu____288 =
              let uu____289 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____289  in
            {
              FStar_TypeChecker_Env.guard_f = uu____288;
              FStar_TypeChecker_Env.deferred =
                (uu___137_287.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_287.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_287.FStar_TypeChecker_Env.implicits)
            }
  
let new_uvar :
  FStar_Range.range ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
          FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    fun binders  ->
      fun k  ->
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____330 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____345 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____345  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                FStar_Pervasives_Native.None r
               in
            let uu____361 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (FStar_Pervasives_Native.Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____361, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____390 = FStar_Syntax_Util.type_u ()  in
        match uu____390 with
        | (t_type,u) ->
            let uu____395 =
              let uu____398 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____398 t_type  in
            (match uu____395 with
             | (tt,uu____400) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of
  ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
     FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
  FStar_Pervasives_Native.tuple2 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____423 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
       FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____449 -> false
  
let __proj__UNIV__item___0 :
  uvi ->
    (FStar_Syntax_Syntax.universe_uvar,FStar_Syntax_Syntax.universe)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
type worklist =
  {
  attempting: FStar_TypeChecker_Common.probs ;
  wl_deferred:
    (Prims.int,Prims.string,FStar_TypeChecker_Common.prob)
      FStar_Pervasives_Native.tuple3 Prims.list
    ;
  ctr: Prims.int ;
  defer_ok: Prims.bool ;
  smt_ok: Prims.bool ;
  tcenv: FStar_TypeChecker_Env.env }
type solution =
  | Success of FStar_TypeChecker_Common.deferred 
  | Failed of (FStar_TypeChecker_Common.prob,Prims.string)
  FStar_Pervasives_Native.tuple2 
let uu___is_Success : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____537 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____551 -> false
  
let __proj__Failed__item___0 :
  solution ->
    (FStar_TypeChecker_Common.prob,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____568 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____572 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____576 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_593  ->
    match uu___105_593 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____606 =
    let uu____607 = FStar_Syntax_Subst.compress t  in
    uu____607.FStar_Syntax_Syntax.n  in
  match uu____606 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____624 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____628 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____624 uu____628
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____631;
         FStar_Syntax_Syntax.pos = uu____632;
         FStar_Syntax_Syntax.vars = uu____633;_},args)
      ->
      let uu____661 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____665 = FStar_Syntax_Print.term_to_string ty  in
      let uu____666 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____661 uu____665 uu____666
  | uu____667 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_673  ->
      match uu___106_673 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____677 =
            let uu____679 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____680 =
              let uu____682 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____683 =
                let uu____685 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____686 =
                  let uu____688 =
                    let uu____690 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____691 =
                      let uu____693 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____694 =
                        let uu____696 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (FStar_Pervasives_Native.fst
                               p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____697 =
                          let uu____699 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____699]  in
                        uu____696 :: uu____697  in
                      uu____693 :: uu____694  in
                    uu____690 :: uu____691  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____688
                   in
                uu____685 :: uu____686  in
              uu____682 :: uu____683  in
            uu____679 :: uu____680  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____677
      | FStar_TypeChecker_Common.CProb p ->
          let uu____704 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____705 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____704
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____705
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_711  ->
      match uu___107_711 with
      | UNIV (u,t) ->
          let x =
            let uu____715 = FStar_Options.hide_uvar_nums ()  in
            if uu____715
            then "?"
            else
              (let uu____717 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____717 FStar_Util.string_of_int)
             in
          let uu____719 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____719
      | TERM ((u,uu____721),t) ->
          let x =
            let uu____726 = FStar_Options.hide_uvar_nums ()  in
            if uu____726
            then "?"
            else
              (let uu____728 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____728 FStar_Util.string_of_int)
             in
          let uu____732 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____732
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____741 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____741 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____749 =
      let uu____751 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____751
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____749 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____769 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____777  ->
            match uu____777 with
            | (x,uu____781) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____769 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____786 =
      let uu____787 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____787  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____786;
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
        let uu___138_800 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___138_800.wl_deferred);
          ctr = (uu___138_800.ctr);
          defer_ok = (uu___138_800.defer_ok);
          smt_ok;
          tcenv = (uu___138_800.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___139_825 = empty_worklist env  in
  let uu____826 = FStar_List.map FStar_Pervasives_Native.snd g  in
  {
    attempting = uu____826;
    wl_deferred = (uu___139_825.wl_deferred);
    ctr = (uu___139_825.ctr);
    defer_ok = false;
    smt_ok = (uu___139_825.smt_ok);
    tcenv = (uu___139_825.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_838 = wl  in
        {
          attempting = (uu___140_838.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_838.ctr);
          defer_ok = (uu___140_838.defer_ok);
          smt_ok = (uu___140_838.smt_ok);
          tcenv = (uu___140_838.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___141_850 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_850.wl_deferred);
        ctr = (uu___141_850.ctr);
        defer_ok = (uu___141_850.defer_ok);
        smt_ok = (uu___141_850.smt_ok);
        tcenv = (uu___141_850.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____861 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____861
         then
           let uu____862 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____862
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_866  ->
    match uu___108_866 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___142_882 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_882.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_882.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_882.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_882.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_882.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_882.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_882.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_903  ->
    match uu___109_903 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_919  ->
      match uu___110_919 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_922  ->
    match uu___111_922 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_931  ->
    match uu___112_931 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_941  ->
    match uu___113_941 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_951  ->
    match uu___114_951 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun uu___115_962  ->
    match uu___115_962 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_973  ->
    match uu___116_973 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_982  ->
    match uu___117_982 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____996 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____996 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1007  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1057 = next_pid ()  in
  let uu____1058 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1057;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1058;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1105 = next_pid ()  in
  let uu____1106 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1105;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1106;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1147 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1147;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = (p_guard orig);
    FStar_TypeChecker_Common.scope = (p_scope orig);
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = FStar_Pervasives_Native.None
  } 
let guard_on_element wl problem x phi =
  match problem.FStar_TypeChecker_Common.element with
  | FStar_Pervasives_Native.None  ->
      let u =
        (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
          x.FStar_Syntax_Syntax.sort
         in
      FStar_Syntax_Util.mk_forall u x phi
  | FStar_Pervasives_Native.Some e ->
      FStar_Syntax_Subst.subst [FStar_Syntax_Syntax.NT (x, e)] phi
  
let explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> Prims.string
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____1199 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1199
        then
          let uu____1200 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1201 = prob_to_string env d  in
          let uu____1202 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1200 uu____1201 uu____1202 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1207 -> failwith "impossible"  in
           let uu____1208 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1216 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1217 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1216, uu____1217)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1221 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1222 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1221, uu____1222)
              in
           match uu____1208 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1231  ->
            match uu___118_1231 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1238 ->
                     FStar_Unionfind.change u
                       (FStar_Pervasives_Native.Some t))
            | TERM ((u,uu____1241),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1264  ->
           match uu___119_1264 with
           | UNIV uu____1266 -> FStar_Pervasives_Native.None
           | TERM ((u,uu____1270),t) ->
               let uu____1274 = FStar_Unionfind.equivalent uv u  in
               if uu____1274
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
    FStar_Unionfind.uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1293  ->
           match uu___120_1293 with
           | UNIV (u',t) ->
               let uu____1297 = FStar_Unionfind.equivalent u u'  in
               if uu____1297
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____1301 -> FStar_Pervasives_Native.None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1308 =
        let uu____1309 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1309
         in
      FStar_Syntax_Subst.compress uu____1308
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1316 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1316
  
let norm_arg env t =
  let uu____1335 = sn env (FStar_Pervasives_Native.fst t)  in
  (uu____1335, (FStar_Pervasives_Native.snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1352  ->
              match uu____1352 with
              | (x,imp) ->
                  let uu____1359 =
                    let uu___143_1360 = x  in
                    let uu____1361 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1360.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1360.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1361
                    }  in
                  (uu____1359, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1376 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1376
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1379 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1379
        | uu____1381 -> u2  in
      let uu____1382 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1382
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then
          ((x.FStar_Syntax_Syntax.sort),
            (FStar_Pervasives_Native.Some (x, phi)))
        else
          (let uu____1489 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1489 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1501;
               FStar_Syntax_Syntax.pos = uu____1502;
               FStar_Syntax_Syntax.vars = uu____1503;_} ->
               ((x1.FStar_Syntax_Syntax.sort),
                 (FStar_Pervasives_Native.Some (x1, phi1)))
           | tt ->
               let uu____1524 =
                 let uu____1525 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1526 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1525
                   uu____1526
                  in
               failwith uu____1524)
    | FStar_Syntax_Syntax.Tm_uinst uu____1536 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1563 =
             let uu____1564 = FStar_Syntax_Subst.compress t1'  in
             uu____1564.FStar_Syntax_Syntax.n  in
           match uu____1563 with
           | FStar_Syntax_Syntax.Tm_refine uu____1576 -> aux true t1'
           | uu____1581 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1593 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1616 =
             let uu____1617 = FStar_Syntax_Subst.compress t1'  in
             uu____1617.FStar_Syntax_Syntax.n  in
           match uu____1616 with
           | FStar_Syntax_Syntax.Tm_refine uu____1629 -> aux true t1'
           | uu____1634 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_app uu____1646 ->
        if norm
        then (t11, FStar_Pervasives_Native.None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1678 =
             let uu____1679 = FStar_Syntax_Subst.compress t1'  in
             uu____1679.FStar_Syntax_Syntax.n  in
           match uu____1678 with
           | FStar_Syntax_Syntax.Tm_refine uu____1691 -> aux true t1'
           | uu____1696 -> (t11, FStar_Pervasives_Native.None))
    | FStar_Syntax_Syntax.Tm_type uu____1708 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_constant uu____1720 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_name uu____1732 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1744 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1756 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_abs uu____1775 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1801 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_let uu____1821 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_match uu____1840 ->
        (t11, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Tm_meta uu____1867 ->
        let uu____1872 =
          let uu____1873 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1874 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1873
            uu____1874
           in
        failwith uu____1872
    | FStar_Syntax_Syntax.Tm_ascribed uu____1884 ->
        let uu____1902 =
          let uu____1903 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1904 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1903
            uu____1904
           in
        failwith uu____1902
    | FStar_Syntax_Syntax.Tm_delayed uu____1914 ->
        let uu____1935 =
          let uu____1936 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1937 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1936
            uu____1937
           in
        failwith uu____1935
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1947 =
          let uu____1948 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1949 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1948
            uu____1949
           in
        failwith uu____1947
     in
  let uu____1959 = whnf env t1  in aux false uu____1959 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1968 =
        let uu____1978 = empty_worklist env  in
        base_and_refinement env uu____1978 t  in
      FStar_All.pipe_right uu____1968 FStar_Pervasives_Native.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    let uu____2002 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2002, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____2022 = base_and_refinement env wl t  in
  match uu____2022 with
  | (t_base,refinement) ->
      (match refinement with
       | FStar_Pervasives_Native.None  -> trivial_refinement t_base
       | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let force_refinement uu____2081 =
  match uu____2081 with
  | (t_base,refopt) ->
      let uu____2095 =
        match refopt with
        | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
        | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
      (match uu____2095 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2119  ->
      match uu___121_2119 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2123 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2124 =
            let uu____2125 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____2125  in
          let uu____2126 =
            let uu____2127 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____2127  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2123 uu____2124
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2126
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2131 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2132 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2133 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2131 uu____2132
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2133
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____2137 =
      let uu____2139 =
        let uu____2141 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2151  ->
                  match uu____2151 with | (uu____2155,uu____2156,x) -> x))
           in
        FStar_List.append wl.attempting uu____2141  in
      FStar_List.map (wl_prob_to_string wl) uu____2139  in
    FStar_All.pipe_right uu____2137 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2174 =
          let uu____2184 =
            let uu____2185 = FStar_Syntax_Subst.compress k  in
            uu____2185.FStar_Syntax_Syntax.n  in
          match uu____2184 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2226 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2226)
              else
                (let uu____2240 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2240 with
                 | (ys',t1,uu____2261) ->
                     let uu____2274 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____2274))
          | uu____2295 ->
              let uu____2296 =
                let uu____2302 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____2302)  in
              ((ys, t), uu____2296)
           in
        match uu____2174 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Util.Inr (FStar_Parser_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2357 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2357 c  in
               let uu____2359 =
                 let uu____2366 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36)
                    in
                 FStar_All.pipe_right uu____2366
                   (fun _0_37  -> FStar_Pervasives_Native.Some _0_37)
                  in
               FStar_Syntax_Util.abs ys1 t1 uu____2359)
  
let solve_prob' :
  Prims.bool ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        uvi Prims.list -> worklist -> worklist
  =
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            let phi =
              match logical_guard with
              | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
              | FStar_Pervasives_Native.Some phi -> phi  in
            let uu____2417 = p_guard prob  in
            match uu____2417 with
            | (uu____2420,uv) ->
                ((let uu____2423 =
                    let uu____2424 = FStar_Syntax_Subst.compress uv  in
                    uu____2424.FStar_Syntax_Syntax.n  in
                  match uu____2423 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2444 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2444
                        then
                          let uu____2445 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2446 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2447 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2445
                            uu____2446 uu____2447
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2451 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2454 = wl  in
                  {
                    attempting = (uu___144_2454.attempting);
                    wl_deferred = (uu___144_2454.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2454.defer_ok);
                    smt_ok = (uu___144_2454.smt_ok);
                    tcenv = (uu___144_2454.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2467 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2467
         then
           let uu____2468 = FStar_Util.string_of_int pid  in
           let uu____2469 =
             let uu____2470 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2470 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2468 uu____2469
         else ());
        commit sol;
        (let uu___145_2475 = wl  in
         {
           attempting = (uu___145_2475.attempting);
           wl_deferred = (uu___145_2475.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2475.defer_ok);
           smt_ok = (uu___145_2475.smt_ok);
           tcenv = (uu___145_2475.tcenv)
         })
  
let solve_prob :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      uvi Prims.list -> worklist -> worklist
  =
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          let conj_guard1 t g =
            match (t, g) with
            | (uu____2504,FStar_TypeChecker_Common.Trivial ) -> t
            | (FStar_Pervasives_Native.None
               ,FStar_TypeChecker_Common.NonTrivial f) ->
                FStar_Pervasives_Native.Some f
            | (FStar_Pervasives_Native.Some
               t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2512 = FStar_Syntax_Util.mk_conj t1 f  in
                FStar_Pervasives_Native.Some uu____2512
             in
          (let uu____2518 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2518
           then
             let uu____2519 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2520 =
               let uu____2521 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2521 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2519 uu____2520
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2546 =
    let uu____2550 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2550 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2546
    (FStar_Util.for_some
       (fun uu____2571  ->
          match uu____2571 with
          | (uv,uu____2579) ->
              FStar_Unionfind.equivalent uv (FStar_Pervasives_Native.fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2623 = occurs wl uk t  in Prims.op_Negation uu____2623  in
  let msg =
    if occurs_ok
    then FStar_Pervasives_Native.None
    else
      (let uu____2628 =
         let uu____2629 =
           FStar_Syntax_Print.uvar_to_string (FStar_Pervasives_Native.fst uk)
            in
         let uu____2633 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2629 uu____2633
          in
       FStar_Pervasives_Native.Some uu____2628)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2681 = occurs_check env wl uk t  in
  match uu____2681 with
  | (occurs_ok,msg) ->
      let uu____2698 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2698, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  ->
            fun x  -> FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set1 v1  in
  let uu____2762 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2786  ->
            fun uu____2787  ->
              match (uu____2786, uu____2787) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2830 =
                    let uu____2831 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2831  in
                  if uu____2830
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2845 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2845
                     then
                       let uu____2852 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2852)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2762 with | (isect,uu____2874) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2923  ->
          fun uu____2924  ->
            match (uu____2923, uu____2924) with
            | ((a,uu____2934),(b,uu____2936)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2980 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2986  ->
                match uu____2986 with
                | (b,uu____2990) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2980
      then FStar_Pervasives_Native.None
      else
        FStar_Pervasives_Native.Some (a, (FStar_Pervasives_Native.snd hd1))
  | uu____2999 -> FStar_Pervasives_Native.None 
let rec pat_vars :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun seen  ->
      fun args  ->
        match args with
        | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
        | hd1::rest ->
            let uu____3042 = pat_var_opt env seen hd1  in
            (match uu____3042 with
             | FStar_Pervasives_Native.None  ->
                 ((let uu____3050 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____3050
                   then
                     let uu____3051 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (FStar_Pervasives_Native.fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3051
                   else ());
                  FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some x ->
                 pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3063 =
      let uu____3064 = FStar_Syntax_Subst.compress t  in
      uu____3064.FStar_Syntax_Syntax.n  in
    match uu____3063 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3067 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3076;
           FStar_Syntax_Syntax.tk = uu____3077;
           FStar_Syntax_Syntax.pos = uu____3078;
           FStar_Syntax_Syntax.vars = uu____3079;_},uu____3080)
        -> true
    | uu____3103 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3165;
         FStar_Syntax_Syntax.pos = uu____3166;
         FStar_Syntax_Syntax.vars = uu____3167;_},args)
      -> (t, uv, k, args)
  | uu____3208 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____3262 = destruct_flex_t t  in
  match uu____3262 with
  | (t1,uv,k,args) ->
      let uu____3330 = pat_vars env [] args  in
      (match uu____3330 with
       | FStar_Pervasives_Native.Some vars ->
           ((t1, uv, k, args), (FStar_Pervasives_Native.Some vars))
       | uu____3386 -> ((t1, uv, k, args), FStar_Pervasives_Native.None))
  
type match_result =
  | MisMatch of
  (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3435 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option,FStar_Syntax_Syntax.delta_depth
                                                                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3458 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3462 -> false
  
let head_match : match_result -> match_result =
  fun uu___122_3465  ->
    match uu___122_3465 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3474 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3487 ->
          let uu____3488 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3488 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.Delta_constant
           | uu____3498 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3512 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3518 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____3540 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____3541 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____3542 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____3551 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____3559 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3576) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3582,uu____3583) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3613) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3628;
             FStar_Syntax_Syntax.index = uu____3629;
             FStar_Syntax_Syntax.sort = t2;_},uu____3631)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3638 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3639 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3640 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3648 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3664 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____3664
  
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
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____3683 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3683
            then FullMatch
            else
              (let uu____3685 =
                 let uu____3690 =
                   let uu____3692 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____3692  in
                 let uu____3693 =
                   let uu____3695 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____3695  in
                 (uu____3690, uu____3693)  in
               MisMatch uu____3685)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3699),FStar_Syntax_Syntax.Tm_uinst (g,uu____3701)) ->
            let uu____3710 = head_matches env f g  in
            FStar_All.pipe_right uu____3710 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            if c = d
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3717),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3719)) ->
            let uu____3744 = FStar_Unionfind.equivalent uv uv'  in
            if uu____3744
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3752),FStar_Syntax_Syntax.Tm_refine (y,uu____3754)) ->
            let uu____3763 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3763 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3765),uu____3766) ->
            let uu____3771 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3771 head_match
        | (uu____3772,FStar_Syntax_Syntax.Tm_refine (x,uu____3774)) ->
            let uu____3779 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3779 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3780,FStar_Syntax_Syntax.Tm_type
           uu____3781) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3782,FStar_Syntax_Syntax.Tm_arrow uu____3783) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3799),FStar_Syntax_Syntax.Tm_app (head',uu____3801))
            ->
            let uu____3830 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3830 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3832),uu____3833) ->
            let uu____3848 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3848 head_match
        | (uu____3849,FStar_Syntax_Syntax.Tm_app (head1,uu____3851)) ->
            let uu____3866 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3866 head_match
        | uu____3867 ->
            let uu____3870 =
              let uu____3875 = delta_depth_of_term env t11  in
              let uu____3877 = delta_depth_of_term env t21  in
              (uu____3875, uu____3877)  in
            MisMatch uu____3870
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3913 = FStar_Syntax_Util.head_and_args t  in
    match uu____3913 with
    | (head1,uu____3925) ->
        let uu____3940 =
          let uu____3941 = FStar_Syntax_Util.un_uinst head1  in
          uu____3941.FStar_Syntax_Syntax.n  in
        (match uu____3940 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3946 =
               let uu____3947 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3947 FStar_Option.isSome  in
             if uu____3946
             then
               let uu____3961 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3961
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)
             else FStar_Pervasives_Native.None
         | uu____3964 -> FStar_Pervasives_Native.None)
     in
  let success d r t11 t21 =
    (r,
      (if d > (Prims.parse_int "0")
       then FStar_Pervasives_Native.Some (t11, t21)
       else FStar_Pervasives_Native.None))
     in
  let fail r = (r, FStar_Pervasives_Native.None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch
        (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Delta_equational
         ),uu____4032)
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4042 =
             let uu____4047 = maybe_inline t11  in
             let uu____4049 = maybe_inline t21  in (uu____4047, uu____4049)
              in
           match uu____4042 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (uu____4070,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Delta_equational ))
        ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4080 =
             let uu____4085 = maybe_inline t11  in
             let uu____4087 = maybe_inline t21  in (uu____4085, uu____4087)
              in
           match uu____4080 with
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
               fail r
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.None )
               -> aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some t22)
               -> aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (FStar_Pervasives_Native.Some t12,FStar_Pervasives_Native.Some
              t22) -> aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2)
        when d1 = d2 ->
        let uu____4112 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____4112 with
         | FStar_Pervasives_Native.None  -> fail r
         | FStar_Pervasives_Native.Some d ->
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
    | MisMatch
        (FStar_Pervasives_Native.Some d1,FStar_Pervasives_Native.Some d2) ->
        let d1_greater_than_d2 =
          FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
        let uu____4127 =
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
             let uu____4135 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____4135))
           in
        (match uu____4127 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4143 -> fail r
    | uu____4148 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                              FStar_Range.range -> FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4177 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.binders ->
                                FStar_Range.range -> FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4207 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4222 = FStar_Syntax_Util.type_u ()  in
      match uu____4222 with
      | (t,uu____4226) ->
          let uu____4227 = new_uvar r binders t  in
          FStar_Pervasives_Native.fst uu____4227
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4236 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____4236 FStar_Pervasives_Native.fst
  
let rec decompose :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (tc Prims.list -> FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term ->
                                                   Prims.bool,(FStar_Syntax_Syntax.binder
                                                                 FStar_Pervasives_Native.option,
                                                                variance,
                                                                tc)
                                                                FStar_Pervasives_Native.tuple3
                                                                Prims.list)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      let matches t' =
        let uu____4278 = head_matches env t1 t'  in
        match uu____4278 with
        | MisMatch uu____4279 -> false
        | uu____4284 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4344,imp),T (t2,uu____4347)) -> (t2, imp)
                     | uu____4364 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4404  ->
                    match uu____4404 with
                    | (t2,uu____4412) ->
                        (FStar_Pervasives_Native.None, INVARIANT,
                          (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____4442 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____4442 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4495))::tcs2) ->
                       aux
                         (((let uu___146_4517 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4517.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4517.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4527 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___123_4558 =
                 match uu___123_4558 with
                 | [] ->
                     FStar_List.rev
                       ((FStar_Pervasives_Native.None, COVARIANT, (C c1)) ::
                       out)
                 | hd1::rest ->
                     decompose1
                       (((FStar_Pervasives_Native.Some hd1), CONTRAVARIANT,
                          (T
                             (((FStar_Pervasives_Native.fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____4621 = decompose1 [] bs1  in
               (rebuild, matches, uu____4621))
      | uu____4649 ->
          let rebuild uu___124_4654 =
            match uu___124_4654 with
            | [] -> t1
            | uu____4656 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4675  ->
    match uu___125_4675 with
    | T (t,uu____4677) -> t
    | uu____4686 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4689  ->
    match uu___126_4689 with
    | T (t,uu____4691) -> FStar_Syntax_Syntax.as_arg t
    | uu____4700 -> failwith "Impossible"
  
let imitation_sub_probs :
  FStar_TypeChecker_Common.prob ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.args ->
          (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option,
            variance,tc) FStar_Pervasives_Native.tuple3 Prims.list ->
            (FStar_TypeChecker_Common.prob Prims.list,tc Prims.list,FStar_Syntax_Syntax.formula)
              FStar_Pervasives_Native.tuple3
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
              | (uu____4769,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4788 = new_uvar r scope1 k  in
                  (match uu____4788 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4800 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args))
                               FStar_Pervasives_Native.None r
                          in
                       let uu____4815 =
                         let uu____4816 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti
                             FStar_Pervasives_Native.None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4816
                          in
                       ((T (gi_xs, mk_kind)), uu____4815))
              | (uu____4825,uu____4826,C uu____4827) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4914 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4925;
                         FStar_Syntax_Syntax.pos = uu____4926;
                         FStar_Syntax_Syntax.vars = uu____4927;_})
                        ->
                        let uu____4942 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4942 with
                         | (T (gi_xs,uu____4958),prob) ->
                             let uu____4968 =
                               let uu____4969 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4969
                                in
                             (uu____4968, [prob])
                         | uu____4971 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4981;
                         FStar_Syntax_Syntax.pos = uu____4982;
                         FStar_Syntax_Syntax.vars = uu____4983;_})
                        ->
                        let uu____4998 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4998 with
                         | (T (gi_xs,uu____5014),prob) ->
                             let uu____5024 =
                               let uu____5025 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5025
                                in
                             (uu____5024, [prob])
                         | uu____5027 -> failwith "impossible")
                    | (uu____5033,uu____5034,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5036;
                         FStar_Syntax_Syntax.pos = uu____5037;
                         FStar_Syntax_Syntax.vars = uu____5038;_})
                        ->
                        let components =
                          FStar_All.pipe_right
                            c.FStar_Syntax_Syntax.effect_args
                            (FStar_List.map
                               (fun t  ->
                                  (FStar_Pervasives_Native.None, INVARIANT,
                                    (T
                                       ((FStar_Pervasives_Native.fst t),
                                         generic_kind)))))
                           in
                        let components1 =
                          (FStar_Pervasives_Native.None, COVARIANT,
                            (T
                               ((c.FStar_Syntax_Syntax.result_typ),
                                 kind_type)))
                          :: components  in
                        let uu____5112 =
                          let uu____5117 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____5117 FStar_List.unzip
                           in
                        (match uu____5112 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5146 =
                                 let uu____5147 =
                                   let uu____5150 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____5150 un_T  in
                                 let uu____5151 =
                                   let uu____5157 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____5157
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5147;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5151;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5146
                                in
                             ((C gi_xs), sub_probs))
                    | uu____5162 ->
                        let uu____5169 = sub_prob scope1 args q  in
                        (match uu____5169 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____4914 with
                   | (tc,probs) ->
                       let uu____5187 =
                         match q with
                         | (FStar_Pervasives_Native.Some
                            b,uu____5213,uu____5214) ->
                             let uu____5222 =
                               let uu____5226 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____5226 :: args  in
                             ((FStar_Pervasives_Native.Some b), (b ::
                               scope1), uu____5222)
                         | uu____5244 ->
                             (FStar_Pervasives_Native.None, scope1, args)
                          in
                       (match uu____5187 with
                        | (bopt,scope2,args1) ->
                            let uu____5287 = aux scope2 args1 qs2  in
                            (match uu____5287 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____5308 =
                                         let uu____5310 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         f :: uu____5310  in
                                       FStar_Syntax_Util.mk_conj_l uu____5308
                                   | FStar_Pervasives_Native.Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____5323 =
                                         let uu____5325 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (FStar_Pervasives_Native.fst b)
                                             f
                                            in
                                         let uu____5326 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives_Native.fst))
                                            in
                                         uu____5325 :: uu____5326  in
                                       FStar_Syntax_Util.mk_conj_l uu____5323
                                    in
                                 ((FStar_List.append probs sub_probs), (tc ::
                                   tcs), f1))))
               in
            aux scope ps qs
  
type flex_t =
  (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ,
    FStar_Syntax_Syntax.args) FStar_Pervasives_Native.tuple4
type im_or_proj_t =
  (((FStar_Syntax_Syntax.uvar,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple2,FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
     FStar_Pervasives_Native.tuple3,FStar_Syntax_Syntax.arg Prims.list,
    (tc Prims.list -> FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ ->
                                                Prims.bool,(FStar_Syntax_Syntax.binder
                                                              FStar_Pervasives_Native.option,
                                                             variance,
                                                             tc)
                                                             FStar_Pervasives_Native.tuple3
                                                             Prims.list)
      FStar_Pervasives_Native.tuple3)
    FStar_Pervasives_Native.tuple3
let rigid_rigid : Prims.int = (Prims.parse_int "0") 
let flex_rigid_eq : Prims.int = (Prims.parse_int "1") 
let flex_refine_inner : Prims.int = (Prims.parse_int "2") 
let flex_refine : Prims.int = (Prims.parse_int "3") 
let flex_rigid : Prims.int = (Prims.parse_int "4") 
let rigid_flex : Prims.int = (Prims.parse_int "5") 
let refine_flex : Prims.int = (Prims.parse_int "6") 
let flex_flex : Prims.int = (Prims.parse_int "7") 
let compress_tprob wl p =
  let uu___147_5379 = p  in
  let uu____5382 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____5383 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5379.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5382;
    FStar_TypeChecker_Common.relation =
      (uu___147_5379.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5383;
    FStar_TypeChecker_Common.element =
      (uu___147_5379.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5379.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5379.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5379.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5379.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5379.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5393 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____5393
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5398 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int,FStar_TypeChecker_Common.prob)
        FStar_Pervasives_Native.tuple2
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5412 = compress_prob wl pr  in
        FStar_All.pipe_right uu____5412 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5418 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____5418 with
           | (lh,uu____5431) ->
               let uu____5446 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____5446 with
                | (rh,uu____5459) ->
                    let uu____5474 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5483,FStar_Syntax_Syntax.Tm_uvar uu____5484)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5503,uu____5504)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5515,FStar_Syntax_Syntax.Tm_uvar uu____5516)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5527,uu____5528)
                          ->
                          let uu____5537 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5537 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (flex_rigid, tp)
                                | uu____5577 ->
                                    let rank =
                                      let uu____5584 = is_top_level_prob prob
                                         in
                                      if uu____5584
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5586 =
                                      let uu___148_5589 = tp  in
                                      let uu____5592 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5589.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5589.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5589.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5592;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5589.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5589.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5589.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5589.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5589.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5589.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5586)))
                      | (uu____5602,FStar_Syntax_Syntax.Tm_uvar uu____5603)
                          ->
                          let uu____5612 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5612 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | FStar_Pervasives_Native.None  ->
                                    (rigid_flex, tp)
                                | uu____5652 ->
                                    let uu____5658 =
                                      let uu___149_5663 = tp  in
                                      let uu____5666 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5663.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5666;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5663.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5663.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5663.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5663.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5663.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5663.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5663.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5663.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5658)))
                      | (uu____5682,uu____5683) -> (rigid_rigid, tp)  in
                    (match uu____5474 with
                     | (rank,tp1) ->
                         let uu____5694 =
                           FStar_All.pipe_right
                             (let uu___150_5697 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5697.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5697.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5697.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5697.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5697.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5697.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5697.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5697.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5697.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43)
                            in
                         (rank, uu____5694))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5703 =
            FStar_All.pipe_right
              (let uu___151_5706 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5706.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5706.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5706.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5706.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5706.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5706.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5706.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5706.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5706.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
             in
          (rigid_rigid, uu____5703)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob FStar_Pervasives_Native.option,FStar_TypeChecker_Common.prob
                                                                    Prims.list,
      Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun wl  ->
    let rec aux uu____5738 probs =
      match uu____5738 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5768 = rank wl hd1  in
               (match uu____5768 with
                | (rank1,hd2) ->
                    if rank1 <= flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           ((FStar_Pervasives_Native.Some hd2),
                             (FStar_List.append out (m :: tl1)), rank1))
                    else
                      if rank1 < min_rank
                      then
                        (match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2),
                                 out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               (rank1, (FStar_Pervasives_Native.Some hd2), (m
                                 :: out)) tl1)
                      else aux (min_rank, min1, (hd2 :: out)) tl1))
       in
    aux
      ((flex_flex + (Prims.parse_int "1")), FStar_Pervasives_Native.None, [])
      wl.attempting
  
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
    match projectee with | UDeferred _0 -> true | uu____5836 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5848 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5860 -> false
  
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
                        let uu____5897 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5897 with
                        | (k,uu____5901) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5906 -> false)))
            | uu____5907 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5950 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5950 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5953 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5959 =
                     let uu____5960 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5961 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5960
                       uu____5961
                      in
                   UFailed uu____5959)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5977 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5977 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5995 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5995 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____5998 ->
                let uu____6001 =
                  let uu____6002 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____6003 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6002
                    uu____6003 msg
                   in
                UFailed uu____6001
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6004,uu____6005) ->
              let uu____6006 =
                let uu____6007 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6008 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6007 uu____6008
                 in
              failwith uu____6006
          | (FStar_Syntax_Syntax.U_unknown ,uu____6009) ->
              let uu____6010 =
                let uu____6011 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6012 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6011 uu____6012
                 in
              failwith uu____6010
          | (uu____6013,FStar_Syntax_Syntax.U_bvar uu____6014) ->
              let uu____6015 =
                let uu____6016 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6017 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6016 uu____6017
                 in
              failwith uu____6015
          | (uu____6018,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6019 =
                let uu____6020 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6021 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6020 uu____6021
                 in
              failwith uu____6019
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6033 = FStar_Unionfind.equivalent v1 v2  in
              if uu____6033
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____6044 = occurs_univ v1 u3  in
              if uu____6044
              then
                let uu____6045 =
                  let uu____6046 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6047 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6046 uu____6047
                   in
                try_umax_components u11 u21 uu____6045
              else
                (let uu____6049 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6049)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____6057 = occurs_univ v1 u3  in
              if uu____6057
              then
                let uu____6058 =
                  let uu____6059 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6060 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6059 uu____6060
                   in
                try_umax_components u11 u21 uu____6058
              else
                (let uu____6062 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6062)
          | (FStar_Syntax_Syntax.U_max uu____6065,uu____6066) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6071 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6071
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6073,FStar_Syntax_Syntax.U_max uu____6074) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6079 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6079
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6081,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6082,FStar_Syntax_Syntax.U_name
             uu____6083) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6084) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6085) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6086,FStar_Syntax_Syntax.U_succ
             uu____6087) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6088,FStar_Syntax_Syntax.U_zero
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
  let uu____6150 = bc1  in
  match uu____6150 with
  | (bs1,mk_cod1) ->
      let uu____6175 = bc2  in
      (match uu____6175 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6222 = FStar_Util.first_N n1 bs  in
             match uu____6222 with
             | (bs3,rest) ->
                 let uu____6236 = mk_cod rest  in (bs3, uu____6236)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____6254 =
               let uu____6258 = mk_cod1 []  in (bs1, uu____6258)  in
             let uu____6260 =
               let uu____6264 = mk_cod2 []  in (bs2, uu____6264)  in
             (uu____6254, uu____6260)
           else
             if l1 > l2
             then
               (let uu____6286 = curry l2 bs1 mk_cod1  in
                let uu____6293 =
                  let uu____6297 = mk_cod2 []  in (bs2, uu____6297)  in
                (uu____6286, uu____6293))
             else
               (let uu____6306 =
                  let uu____6310 = mk_cod1 []  in (bs1, uu____6310)  in
                let uu____6312 = curry l1 bs2 mk_cod2  in
                (uu____6306, uu____6312)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6416 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____6416
       then
         let uu____6417 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6417
       else ());
      (let uu____6419 = next_prob probs  in
       match uu____6419 with
       | (FStar_Pervasives_Native.Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6432 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6432.wl_deferred);
               ctr = (uu___152_6432.ctr);
               defer_ok = (uu___152_6432.defer_ok);
               smt_ok = (uu___152_6432.smt_ok);
               tcenv = (uu___152_6432.tcenv)
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
                  let uu____6439 = solve_flex_rigid_join env tp probs1  in
                  (match uu____6439 with
                   | FStar_Pervasives_Native.None  ->
                       solve_t' env (maybe_invert tp) probs1
                   | FStar_Pervasives_Native.Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6443 = solve_rigid_flex_meet env tp probs1  in
                     match uu____6443 with
                     | FStar_Pervasives_Native.None  ->
                         solve_t' env (maybe_invert tp) probs1
                     | FStar_Pervasives_Native.Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (FStar_Pervasives_Native.None ,uu____6447,uu____6448) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6457 ->
                let uu____6462 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6490  ->
                          match uu____6490 with
                          | (c,uu____6495,uu____6496) -> c < probs.ctr))
                   in
                (match uu____6462 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6518 =
                            FStar_List.map
                              (fun uu____6524  ->
                                 match uu____6524 with
                                 | (uu____6530,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____6518
                      | uu____6533 ->
                          let uu____6538 =
                            let uu___153_6539 = probs  in
                            let uu____6540 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6549  ->
                                      match uu____6549 with
                                      | (uu____6553,uu____6554,y) -> y))
                               in
                            {
                              attempting = uu____6540;
                              wl_deferred = rest;
                              ctr = (uu___153_6539.ctr);
                              defer_ok = (uu___153_6539.defer_ok);
                              smt_ok = (uu___153_6539.smt_ok);
                              tcenv = (uu___153_6539.tcenv)
                            }  in
                          solve env uu____6538))))

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
            let uu____6561 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____6561 with
            | USolved wl1 ->
                let uu____6563 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____6563
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
                  let uu____6597 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6597 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6600 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6608;
                  FStar_Syntax_Syntax.pos = uu____6609;
                  FStar_Syntax_Syntax.vars = uu____6610;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6613;
                  FStar_Syntax_Syntax.pos = uu____6614;
                  FStar_Syntax_Syntax.vars = uu____6615;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6627,uu____6628) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6633,FStar_Syntax_Syntax.Tm_uinst uu____6634) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6639 -> USolved wl

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
            ((let uu____6647 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6647
              then
                let uu____6648 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6648 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6656 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6656
         then
           let uu____6657 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6657
         else ());
        (let uu____6659 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6659 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6701 = head_matches_delta env () t1 t2  in
               match uu____6701 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6723 -> FStar_Pervasives_Native.None
                    | FullMatch  ->
                        (match ts with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.Some (t1, [])
                         | FStar_Pervasives_Native.Some (t11,t21) ->
                             FStar_Pervasives_Native.Some (t11, []))
                    | HeadMatch  ->
                        let uu____6749 =
                          match ts with
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              let uu____6758 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6759 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6758, uu____6759)
                          | FStar_Pervasives_Native.None  ->
                              let uu____6762 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6763 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6762, uu____6763)
                           in
                        (match uu____6749 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6785 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22
                                   FStar_Pervasives_Native.None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6785
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6808 =
                                    let uu____6814 =
                                      let uu____6817 =
                                        let uu____6820 =
                                          let uu____6821 =
                                            let uu____6826 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____6826)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6821
                                           in
                                        FStar_Syntax_Syntax.mk uu____6820  in
                                      uu____6817 FStar_Pervasives_Native.None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6839 =
                                      let uu____6841 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____6841]  in
                                    (uu____6814, uu____6839)  in
                                  FStar_Pervasives_Native.Some uu____6808
                              | (uu____6850,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6852)) ->
                                  let uu____6857 =
                                    let uu____6861 =
                                      let uu____6863 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____6863]  in
                                    (t11, uu____6861)  in
                                  FStar_Pervasives_Native.Some uu____6857
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6869),uu____6870) ->
                                  let uu____6875 =
                                    let uu____6879 =
                                      let uu____6881 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____6881]  in
                                    (t21, uu____6879)  in
                                  FStar_Pervasives_Native.Some uu____6875
                              | uu____6886 ->
                                  let uu____6889 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____6889 with
                                   | (head1,uu____6904) ->
                                       let uu____6919 =
                                         let uu____6920 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6920.FStar_Syntax_Syntax.n  in
                                       (match uu____6919 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6927;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6929;_}
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
                                        | uu____6938 ->
                                            FStar_Pervasives_Native.None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6947) ->
                  let uu____6960 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6969  ->
                            match uu___127_6969 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | FStar_Pervasives_Native.Some rank1 when
                                     is_rigid_flex rank1 ->
                                     let uu____6974 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6974 with
                                      | (u',uu____6985) ->
                                          let uu____7000 =
                                            let uu____7001 = whnf env u'  in
                                            uu____7001.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7000 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7005) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7021 -> false))
                                 | uu____7022 -> false)
                            | uu____7024 -> false))
                     in
                  (match uu____6960 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7045 tps =
                         match uu____7045 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] ->
                                  FStar_Pervasives_Native.Some
                                    (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7072 =
                                    let uu____7077 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____7077  in
                                  (match uu____7072 with
                                   | FStar_Pervasives_Native.Some
                                       (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Pervasives_Native.None)
                              | uu____7096 -> FStar_Pervasives_Native.None)
                          in
                       let uu____7101 =
                         let uu____7106 =
                           let uu____7110 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____7110, [])  in
                         make_lower_bound uu____7106 lower_bounds  in
                       (match uu____7101 with
                        | FStar_Pervasives_Native.None  ->
                            ((let uu____7117 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7117
                              then
                                FStar_Util.print_string "No lower bounds\n"
                              else ());
                             FStar_Pervasives_Native.None)
                        | FStar_Pervasives_Native.Some (lhs_bound,sub_probs)
                            ->
                            let eq_prob =
                              new_problem env lhs_bound
                                FStar_TypeChecker_Common.EQ
                                tp.FStar_TypeChecker_Common.rhs
                                FStar_Pervasives_Native.None
                                tp.FStar_TypeChecker_Common.loc
                                "meeting refinements"
                               in
                            ((let uu____7130 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7130
                              then
                                let wl' =
                                  let uu___154_7132 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7132.wl_deferred);
                                    ctr = (uu___154_7132.ctr);
                                    defer_ok = (uu___154_7132.defer_ok);
                                    smt_ok = (uu___154_7132.smt_ok);
                                    tcenv = (uu___154_7132.tcenv)
                                  }  in
                                let uu____7133 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7133
                              else ());
                             (let uu____7135 =
                                solve_t env eq_prob
                                  (let uu___155_7136 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7136.wl_deferred);
                                     ctr = (uu___155_7136.ctr);
                                     defer_ok = (uu___155_7136.defer_ok);
                                     smt_ok = (uu___155_7136.smt_ok);
                                     tcenv = (uu___155_7136.tcenv)
                                   })
                                 in
                              match uu____7135 with
                              | Success uu____7138 ->
                                  let wl1 =
                                    let uu___156_7140 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7140.wl_deferred);
                                      ctr = (uu___156_7140.ctr);
                                      defer_ok = (uu___156_7140.defer_ok);
                                      smt_ok = (uu___156_7140.smt_ok);
                                      tcenv = (uu___156_7140.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      FStar_Pervasives_Native.None [] wl1
                                     in
                                  let uu____7142 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p
                                             FStar_Pervasives_Native.None []
                                             wl3) wl2 lower_bounds
                                     in
                                  FStar_Pervasives_Native.Some wl2
                              | uu____7145 -> FStar_Pervasives_Native.None))))
              | uu____7146 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env ->
    tprob -> worklist -> worklist FStar_Pervasives_Native.option
  =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7153 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____7153
         then
           let uu____7154 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7154
         else ());
        (let uu____7156 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____7156 with
         | (u,args) ->
             let uu____7183 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____7183 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____7214 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____7214 with
                    | (h1,args1) ->
                        let uu____7242 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____7242 with
                         | (h2,uu____7255) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7274 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____7274
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7287 =
                                          let uu____7289 =
                                            let uu____7290 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7290
                                             in
                                          [uu____7289]  in
                                        FStar_Pervasives_Native.Some
                                          uu____7287))
                                  else FStar_Pervasives_Native.None
                              | (FStar_Syntax_Syntax.Tm_name
                                 a,FStar_Syntax_Syntax.Tm_name b) ->
                                  if FStar_Syntax_Syntax.bv_eq a b
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then FStar_Pervasives_Native.Some []
                                     else
                                       (let uu____7312 =
                                          let uu____7314 =
                                            let uu____7315 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2
                                                FStar_Pervasives_Native.None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7315
                                             in
                                          [uu____7314]  in
                                        FStar_Pervasives_Native.Some
                                          uu____7312))
                                  else FStar_Pervasives_Native.None
                              | uu____7323 -> FStar_Pervasives_Native.None))
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
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             let x1 = FStar_Syntax_Syntax.freshen_bv x  in
                             let subst1 =
                               [FStar_Syntax_Syntax.DB
                                  ((Prims.parse_int "0"), x1)]
                                in
                             let phi11 = FStar_Syntax_Subst.subst subst1 phi1
                                in
                             let phi21 = FStar_Syntax_Subst.subst subst1 phi2
                                in
                             let uu____7389 =
                               let uu____7395 =
                                 let uu____7398 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____7398  in
                               (uu____7395, m1)  in
                             FStar_Pervasives_Native.Some uu____7389)
                    | (uu____7407,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7409)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7441),uu____7442) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                    | uu____7473 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some m1 ->
                             FStar_Pervasives_Native.Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7507) ->
                       let uu____7520 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7529  ->
                                 match uu___128_7529 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | FStar_Pervasives_Native.Some rank1
                                          when is_flex_rigid rank1 ->
                                          let uu____7534 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____7534 with
                                           | (u',uu____7545) ->
                                               let uu____7560 =
                                                 let uu____7561 = whnf env u'
                                                    in
                                                 uu____7561.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7560 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7565) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7581 -> false))
                                      | uu____7582 -> false)
                                 | uu____7584 -> false))
                          in
                       (match uu____7520 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7609 tps =
                              match uu____7609 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] ->
                                       FStar_Pervasives_Native.Some
                                         (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7650 =
                                         let uu____7657 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7657  in
                                       (match uu____7650 with
                                        | FStar_Pervasives_Native.Some
                                            (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None)
                                   | uu____7692 ->
                                       FStar_Pervasives_Native.None)
                               in
                            let uu____7699 =
                              let uu____7706 =
                                let uu____7712 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7712, [])  in
                              make_upper_bound uu____7706 upper_bounds  in
                            (match uu____7699 with
                             | FStar_Pervasives_Native.None  ->
                                 ((let uu____7721 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7721
                                   then
                                     FStar_Util.print_string
                                       "No upper bounds\n"
                                   else ());
                                  FStar_Pervasives_Native.None)
                             | FStar_Pervasives_Native.Some
                                 (rhs_bound,sub_probs) ->
                                 let eq_prob =
                                   new_problem env
                                     tp.FStar_TypeChecker_Common.lhs
                                     FStar_TypeChecker_Common.EQ rhs_bound
                                     FStar_Pervasives_Native.None
                                     tp.FStar_TypeChecker_Common.loc
                                     "joining refinements"
                                    in
                                 ((let uu____7740 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7740
                                   then
                                     let wl' =
                                       let uu___157_7742 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7742.wl_deferred);
                                         ctr = (uu___157_7742.ctr);
                                         defer_ok = (uu___157_7742.defer_ok);
                                         smt_ok = (uu___157_7742.smt_ok);
                                         tcenv = (uu___157_7742.tcenv)
                                       }  in
                                     let uu____7743 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7743
                                   else ());
                                  (let uu____7745 =
                                     solve_t env eq_prob
                                       (let uu___158_7746 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7746.wl_deferred);
                                          ctr = (uu___158_7746.ctr);
                                          defer_ok = (uu___158_7746.defer_ok);
                                          smt_ok = (uu___158_7746.smt_ok);
                                          tcenv = (uu___158_7746.tcenv)
                                        })
                                      in
                                   match uu____7745 with
                                   | Success uu____7748 ->
                                       let wl1 =
                                         let uu___159_7750 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7750.wl_deferred);
                                           ctr = (uu___159_7750.ctr);
                                           defer_ok =
                                             (uu___159_7750.defer_ok);
                                           smt_ok = (uu___159_7750.smt_ok);
                                           tcenv = (uu___159_7750.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           FStar_Pervasives_Native.None []
                                           wl1
                                          in
                                       let uu____7752 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p
                                                  FStar_Pervasives_Native.None
                                                  [] wl3) wl2 upper_bounds
                                          in
                                       FStar_Pervasives_Native.Some wl2
                                   | uu____7755 ->
                                       FStar_Pervasives_Native.None))))
                   | uu____7756 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____7821 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____7821
                      then
                        let uu____7822 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7822
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives_Native.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7854 = hd1  in
                      let uu____7855 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7854.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7854.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7855
                      }  in
                    let hd21 =
                      let uu___161_7859 = hd2  in
                      let uu____7860 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7859.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7859.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7860
                      }  in
                    let prob =
                      let uu____7864 =
                        let uu____7867 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7867 hd21.FStar_Syntax_Syntax.sort
                          FStar_Pervasives_Native.None "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7864
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____7875 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7875
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____7878 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____7878 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7896 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives_Native.fst
                              in
                           let uu____7899 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____7896 uu____7899
                            in
                         ((let uu____7905 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7905
                           then
                             let uu____7906 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7907 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7906 uu____7907
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7922 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7928 = aux scope env [] bs1 bs2  in
              match uu____7928 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 =
                    solve_prob orig (FStar_Pervasives_Native.Some phi) [] wl
                     in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7944 = compress_tprob wl problem  in
        solve_t' env uu____7944 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7977 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7977 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____7994,uu____7995) ->
                   let rec may_relate head3 =
                     let uu____8010 =
                       let uu____8011 = FStar_Syntax_Subst.compress head3  in
                       uu____8011.FStar_Syntax_Syntax.n  in
                     match uu____8010 with
                     | FStar_Syntax_Syntax.Tm_name uu____8014 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8015 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | FStar_Syntax_Syntax.Tm_ascribed
                         (t,uu____8033,uu____8034) -> may_relate t
                     | FStar_Syntax_Syntax.Tm_uinst (t,uu____8064) ->
                         may_relate t
                     | FStar_Syntax_Syntax.Tm_meta (t,uu____8070) ->
                         may_relate t
                     | uu____8075 -> false  in
                   let uu____8076 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____8076
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
                            | FStar_Pervasives_Native.Some t ->
                                FStar_Syntax_Util.mk_has_type t11 t t21
                            | FStar_Pervasives_Native.None  ->
                                let x =
                                  FStar_Syntax_Syntax.new_bv
                                    FStar_Pervasives_Native.None t11
                                   in
                                let u_x =
                                  env1.FStar_TypeChecker_Env.universe_of env1
                                    t11
                                   in
                                let uu____8093 =
                                  let uu____8094 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8094 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____8093
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____8096 =
                       solve_prob orig (FStar_Pervasives_Native.Some guard)
                         [] wl1
                        in
                     solve env1 uu____8096
                   else giveup env1 "head mismatch" orig
               | (uu____8098,FStar_Pervasives_Native.Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8106 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8106.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8106.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8106.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8106.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8106.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8106.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8106.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8106.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8107,FStar_Pervasives_Native.None ) ->
                   ((let uu____8114 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8114
                     then
                       let uu____8115 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____8116 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____8117 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____8118 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8115
                         uu____8116 uu____8117 uu____8118
                     else ());
                    (let uu____8120 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____8120 with
                     | (head11,args1) ->
                         let uu____8146 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____8146 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8186 =
                                  let uu____8187 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____8188 = args_to_string args1  in
                                  let uu____8189 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____8190 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8187 uu____8188 uu____8189
                                    uu____8190
                                   in
                                giveup env1 uu____8186 orig
                              else
                                (let uu____8192 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8195 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____8195 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____8192
                                 then
                                   let uu____8196 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____8196 with
                                   | USolved wl2 ->
                                       let uu____8198 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None []
                                           wl2
                                          in
                                       solve env1 uu____8198
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8202 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____8202 with
                                    | (base1,refinement1) ->
                                        let uu____8228 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____8228 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (FStar_Pervasives_Native.None
                                                 ,FStar_Pervasives_Native.None
                                                 ) ->
                                                  let uu____8282 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____8282 with
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
                                                           (fun uu____8292 
                                                              ->
                                                              fun uu____8293 
                                                                ->
                                                                match 
                                                                  (uu____8292,
                                                                    uu____8293)
                                                                with
                                                                | ((a,uu____8303),
                                                                   (a',uu____8305))
                                                                    ->
                                                                    let uu____8310
                                                                    =
                                                                    mk_problem
                                                                    (p_scope
                                                                    orig)
                                                                    orig a
                                                                    FStar_TypeChecker_Common.EQ
                                                                    a'
                                                                    FStar_Pervasives_Native.None
                                                                    "index"
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    (fun
                                                                    _0_49  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_49)
                                                                    uu____8310)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____8316 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                FStar_Pervasives_Native.fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8316
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (FStar_Pervasives_Native.Some
                                                              formula) [] wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8320 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___163_8353 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8353.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____8373 = p  in
          match uu____8373 with
          | (((u,k),xs,c),ps,(h,uu____8384,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8433 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____8433 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8447 = h gs_xs  in
                     let uu____8448 =
                       let uu____8455 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50)
                          in
                       FStar_All.pipe_right uu____8455
                         (fun _0_51  -> FStar_Pervasives_Native.Some _0_51)
                        in
                     FStar_Syntax_Util.abs xs1 uu____8447 uu____8448  in
                   ((let uu____8486 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8486
                     then
                       let uu____8487 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____8488 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____8489 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____8490 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____8491 =
                         let uu____8492 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____8492
                           (FStar_String.concat ", ")
                          in
                       let uu____8495 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8487 uu____8488 uu____8489 uu____8490
                         uu____8491 uu____8495
                     else ());
                    (let wl2 =
                       solve_prob orig (FStar_Pervasives_Native.Some formula)
                         [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___129_8513 =
          match uu___129_8513 with
          | FStar_Pervasives_Native.None  ->
              giveup env1 "unable to compute subterms" orig
          | FStar_Pervasives_Native.Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____8542 = p  in
          match uu____8542 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8600 = FStar_List.nth ps i  in
              (match uu____8600 with
               | (pi,uu____8603) ->
                   let uu____8608 = FStar_List.nth xs i  in
                   (match uu____8608 with
                    | (xi,uu____8615) ->
                        let rec gs k =
                          let uu____8624 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____8624 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8676)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8684 = new_uvar r xs k_a  in
                                    (match uu____8684 with
                                     | (gi_xs,gi) ->
                                         let gi_xs1 =
                                           FStar_TypeChecker_Normalize.eta_expand
                                             env1 gi_xs
                                            in
                                         let gi_ps =
                                           (FStar_Syntax_Syntax.mk_Tm_app gi
                                              ps)
                                             (FStar_Pervasives_Native.Some
                                                (k_a.FStar_Syntax_Syntax.n))
                                             r
                                            in
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT
                                              (a, gi_xs1))
                                           :: subst1  in
                                         let uu____8703 = aux subst2 tl1  in
                                         (match uu____8703 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8718 =
                                                let uu____8720 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8720 :: gi_xs'  in
                                              let uu____8721 =
                                                let uu____8723 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8723 :: gi_ps'  in
                                              (uu____8718, uu____8721)))
                                 in
                              aux [] bs
                           in
                        let uu____8726 =
                          let uu____8727 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8727
                           in
                        if uu____8726
                        then FStar_Pervasives_Native.None
                        else
                          (let uu____8730 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8730 with
                           | (g_xs,uu____8737) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8744 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     FStar_Pervasives_Native.None r
                                    in
                                 let uu____8749 =
                                   let uu____8756 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52)
                                      in
                                   FStar_All.pipe_right uu____8756
                                     (fun _0_53  ->
                                        FStar_Pervasives_Native.Some _0_53)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8744
                                   uu____8749
                                  in
                               let sub1 =
                                 let uu____8787 =
                                   let uu____8790 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       FStar_Pervasives_Native.None r
                                      in
                                   let uu____8797 =
                                     let uu____8800 =
                                       FStar_List.map
                                         (fun uu____8806  ->
                                            match uu____8806 with
                                            | (uu____8811,uu____8812,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8800  in
                                   mk_problem (p_scope orig) orig uu____8790
                                     (p_rel orig) uu____8797
                                     FStar_Pervasives_Native.None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8787
                                  in
                               ((let uu____8822 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8822
                                 then
                                   let uu____8823 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8824 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8823 uu____8824
                                 else ());
                                (let wl2 =
                                   let uu____8827 =
                                     let uu____8829 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives_Native.fst
                                         (p_guard sub1)
                                        in
                                     FStar_Pervasives_Native.Some uu____8829
                                      in
                                   solve_prob orig uu____8827
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8834 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_55  ->
                                      FStar_Pervasives_Native.Some _0_55)
                                   uu____8834)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8858 = lhs  in
          match uu____8858 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8881 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8881 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8903 =
                        let uu____8929 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____8929)  in
                      FStar_Pervasives_Native.Some uu____8903
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____9012 =
                           let uu____9016 =
                             let uu____9017 = FStar_Syntax_Subst.compress k
                                in
                             uu____9017.FStar_Syntax_Syntax.n  in
                           (uu____9016, args)  in
                         match uu____9012 with
                         | (uu____9024,[]) ->
                             let uu____9026 =
                               let uu____9032 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____9032)  in
                             FStar_Pervasives_Native.Some uu____9026
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9043,uu____9044) ->
                             let uu____9055 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9055 with
                              | (uv1,uv_args) ->
                                  let uu____9084 =
                                    let uu____9085 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9085.FStar_Syntax_Syntax.n  in
                                  (match uu____9084 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9092) ->
                                       let uu____9105 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9105 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9119  ->
                                                      let uu____9120 =
                                                        let uu____9121 =
                                                          let uu____9122 =
                                                            let uu____9125 =
                                                              let uu____9126
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9126
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9125
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9122
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9121
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9120))
                                               in
                                            let c1 =
                                              let uu____9132 =
                                                let uu____9133 =
                                                  let uu____9136 =
                                                    let uu____9137 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9137
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9136
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____9133
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9132
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9146 =
                                                let uu____9153 =
                                                  let uu____9159 =
                                                    let uu____9160 =
                                                      let uu____9163 =
                                                        let uu____9164 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9164
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9163
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9160
                                                     in
                                                  FStar_Util.Inl uu____9159
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____9153
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9146
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9187 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9190,uu____9191)
                             ->
                             let uu____9203 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9203 with
                              | (uv1,uv_args) ->
                                  let uu____9232 =
                                    let uu____9233 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9233.FStar_Syntax_Syntax.n  in
                                  (match uu____9232 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9240) ->
                                       let uu____9253 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9253 with
                                        | FStar_Pervasives_Native.None  ->
                                            FStar_Pervasives_Native.None
                                        | FStar_Pervasives_Native.Some scope
                                            ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9267  ->
                                                      let uu____9268 =
                                                        let uu____9269 =
                                                          let uu____9270 =
                                                            let uu____9273 =
                                                              let uu____9274
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9274
                                                                FStar_Pervasives_Native.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9273
                                                             in
                                                          FStar_Pervasives_Native.fst
                                                            uu____9270
                                                           in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (FStar_Pervasives_Native.Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9269
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9268))
                                               in
                                            let c1 =
                                              let uu____9280 =
                                                let uu____9281 =
                                                  let uu____9284 =
                                                    let uu____9285 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9285
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9284
                                                   in
                                                FStar_Pervasives_Native.fst
                                                  uu____9281
                                                 in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9280
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9294 =
                                                let uu____9301 =
                                                  let uu____9307 =
                                                    let uu____9308 =
                                                      let uu____9311 =
                                                        let uu____9312 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9312
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9311
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9308
                                                     in
                                                  FStar_Util.Inl uu____9307
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____9301
                                                 in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9294
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             FStar_Pervasives_Native.Some
                                               (xs1, c1)))
                                   | uu____9335 ->
                                       FStar_Pervasives_Native.None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9340)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____9366 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____9366
                                 (fun _0_56  ->
                                    FStar_Pervasives_Native.Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9385 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____9385 with
                                  | (args1,rest) ->
                                      let uu____9401 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____9401 with
                                       | (xs2,c2) ->
                                           let uu____9409 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____9409
                                             (fun uu____9420  ->
                                                match uu____9420 with
                                                | (xs',c3) ->
                                                    FStar_Pervasives_Native.Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9442 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____9442 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1)))
                                          FStar_Pervasives_Native.None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9488 =
                                        let uu____9491 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9491
                                         in
                                      FStar_All.pipe_right uu____9488
                                        (fun _0_57  ->
                                           FStar_Pervasives_Native.Some _0_57))
                         | uu____9499 ->
                             let uu____9503 =
                               let uu____9504 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____9508 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____9509 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9504 uu____9508 uu____9509
                                in
                             failwith uu____9503
                          in
                       let uu____9513 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____9513
                         (fun uu____9541  ->
                            match uu____9541 with
                            | (xs1,c1) ->
                                let uu____9569 =
                                  let uu____9592 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9592)
                                   in
                                FStar_Pervasives_Native.Some uu____9569))
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
                     let uu____9664 = imitate orig env wl1 st  in
                     match uu____9664 with
                     | Failed uu____9669 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9675 = project orig env wl1 i st  in
                      match uu____9675 with
                      | FStar_Pervasives_Native.None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some (Failed uu____9682) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | FStar_Pervasives_Native.Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____9696 = FStar_Syntax_Util.head_and_args t21  in
                match uu____9696 with
                | (hd1,uu____9707) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9722 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9730 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9731 -> true
                     | uu____9746 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____9749 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____9749
                         then true
                         else
                           ((let uu____9752 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____9752
                             then
                               let uu____9753 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9753
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9761 =
                    let uu____9764 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____9764
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____9761 FStar_Syntax_Free.names  in
                let uu____9795 = FStar_Util.set_is_empty fvs_hd  in
                if uu____9795
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | FStar_Pervasives_Native.Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____9804 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____9804 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9812 =
                            let uu____9813 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____9813
                             in
                          giveup_or_defer1 orig uu____9812
                        else
                          (let uu____9815 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____9815
                           then
                             let uu____9816 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____9816
                              then
                                let uu____9817 = subterms args_lhs  in
                                imitate' orig env wl1 uu____9817
                              else
                                ((let uu____9821 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____9821
                                  then
                                    let uu____9822 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9823 = names_to_string fvs1  in
                                    let uu____9824 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9822 uu____9823 uu____9824
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9829 ->
                                        let uu____9830 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9830 t21
                                     in
                                  let wl2 =
                                    solve_prob orig
                                      FStar_Pervasives_Native.None
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
                               (let uu____9839 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9839
                                then
                                  ((let uu____9841 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9841
                                    then
                                      let uu____9842 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9843 = names_to_string fvs1
                                         in
                                      let uu____9844 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9842 uu____9843 uu____9844
                                    else ());
                                   (let uu____9846 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9846
                                      (~- (Prims.parse_int "1"))))
                                else
                                  giveup env
                                    "free-variable check failed on a non-redex"
                                    orig)))
               | FStar_Pervasives_Native.None  when patterns_only ->
                   giveup env "not a pattern" orig
               | FStar_Pervasives_Native.None  ->
                   if wl1.defer_ok
                   then solve env (defer "not a pattern" orig wl1)
                   else
                     (let uu____9857 =
                        let uu____9858 = FStar_Syntax_Free.names t1  in
                        check_head uu____9858 t2  in
                      if uu____9857
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9862 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9862
                          then
                            let uu____9863 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9863
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9866 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9866 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9908 =
               match uu____9908 with
               | (t,u,k,args) ->
                   let k1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Beta] env k
                      in
                   let uu____9939 = FStar_Syntax_Util.arrow_formals k1  in
                   (match uu____9939 with
                    | (all_formals,uu____9950) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10042  ->
                                        match uu____10042 with
                                        | (x,imp) ->
                                            let uu____10049 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____10049, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____10057 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____10057 with
                                | (t1,uu____10061) ->
                                    let uu____10062 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    FStar_Pervasives_Native.fst uu____10062
                                 in
                              let uu____10065 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____10065 with
                               | (t',tm_u1) ->
                                   let uu____10072 = destruct_flex_t t'  in
                                   (match uu____10072 with
                                    | (uu____10092,u1,k11,uu____10095) ->
                                        let sol =
                                          let uu____10123 =
                                            let uu____10128 =
                                              u_abs k1 all_formals t'  in
                                            ((u, k1), uu____10128)  in
                                          TERM uu____10123  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1)
                                            FStar_Pervasives_Native.None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k11, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10188 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____10188 with
                               | FStar_Pervasives_Native.None  ->
                                   aux pat_args pattern_vars pattern_var_set
                                     formals1 tl1
                               | FStar_Pervasives_Native.Some y ->
                                   let maybe_pat =
                                     match xs_opt with
                                     | FStar_Pervasives_Native.None  -> true
                                     | FStar_Pervasives_Native.Some xs ->
                                         FStar_All.pipe_right xs
                                           (FStar_Util.for_some
                                              (fun uu____10217  ->
                                                 match uu____10217 with
                                                 | (x,uu____10221) ->
                                                     FStar_Syntax_Syntax.bv_eq
                                                       x
                                                       (FStar_Pervasives_Native.fst
                                                          y)))
                                      in
                                   if Prims.op_Negation maybe_pat
                                   then
                                     aux pat_args pattern_vars
                                       pattern_var_set formals1 tl1
                                   else
                                     (let fvs =
                                        FStar_Syntax_Free.names
                                          (FStar_Pervasives_Native.fst y).FStar_Syntax_Syntax.sort
                                         in
                                      let uu____10227 =
                                        let uu____10228 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____10228  in
                                      if uu____10227
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10232 =
                                           FStar_Util.set_add
                                             (FStar_Pervasives_Native.fst
                                                formal) pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10232 formals1
                                           tl1)))
                          | uu____10238 -> failwith "Impossible"  in
                        let uu____10249 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____10249 all_formals args)
                in
             let solve_both_pats wl1 uu____10297 uu____10298 r =
               match (uu____10297, uu____10298) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10452 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____10452
                   then
                     let uu____10456 =
                       solve_prob orig FStar_Pervasives_Native.None [] wl1
                        in
                     solve env uu____10456
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____10471 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10471
                       then
                         let uu____10472 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____10473 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____10474 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____10475 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____10476 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10472 uu____10473 uu____10474 uu____10475
                           uu____10476
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____10518 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____10518 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10526 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____10526 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10556 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10556
                                     in
                                  let uu____10559 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____10559 k3)
                           else
                             (let uu____10562 =
                                let uu____10563 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____10564 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____10565 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10563 uu____10564 uu____10565
                                 in
                              failwith uu____10562)
                          in
                       let uu____10566 =
                         let uu____10572 =
                           let uu____10580 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____10580  in
                         match uu____10572 with
                         | (bs,k1') ->
                             let uu____10598 =
                               let uu____10606 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____10606
                                in
                             (match uu____10598 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____10627 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        FStar_Pervasives_Native.None
                                        "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10627
                                     in
                                  let uu____10632 =
                                    let uu____10635 =
                                      let uu____10636 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____10636.FStar_Syntax_Syntax.n  in
                                    let uu____10639 =
                                      let uu____10640 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____10640.FStar_Syntax_Syntax.n  in
                                    (uu____10635, uu____10639)  in
                                  (match uu____10632 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10648,uu____10649) ->
                                       (k1', [sub_prob])
                                   | (uu____10653,FStar_Syntax_Syntax.Tm_type
                                      uu____10654) -> (k2', [sub_prob])
                                   | uu____10658 ->
                                       let uu____10661 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____10661 with
                                        | (t,uu____10670) ->
                                            let uu____10671 = new_uvar r zs t
                                               in
                                            (match uu____10671 with
                                             | (k_zs,uu____10680) ->
                                                 let kprob =
                                                   let uu____10682 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs
                                                       FStar_Pervasives_Native.None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10682
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____10566 with
                       | (k_u',sub_probs) ->
                           let uu____10696 =
                             let uu____10704 =
                               let uu____10705 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left
                                 FStar_Pervasives_Native.fst uu____10705
                                in
                             let uu____10710 =
                               let uu____10713 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____10713  in
                             let uu____10716 =
                               let uu____10719 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____10719  in
                             (uu____10704, uu____10710, uu____10716)  in
                           (match uu____10696 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____10738 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____10738 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____10762 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____10762
                                        then
                                          let wl2 =
                                            solve_prob orig
                                              FStar_Pervasives_Native.None
                                              [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____10769 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____10769 with
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
                                                    solve_prob orig
                                                      FStar_Pervasives_Native.None
                                                      [sol1; sol2] wl1
                                                     in
                                                  solve env
                                                    (attempt sub_probs wl2))))))))
                in
             let solve_one_pat uu____10821 uu____10822 =
               match (uu____10821, uu____10822) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10926 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10926
                     then
                       let uu____10927 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10928 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10927 uu____10928
                     else ());
                    (let uu____10930 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____10930
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10940  ->
                              fun uu____10941  ->
                                match (uu____10940, uu____10941) with
                                | ((a,uu____10951),(t21,uu____10953)) ->
                                    let uu____10958 =
                                      let uu____10961 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10961
                                        FStar_TypeChecker_Common.EQ t21
                                        FStar_Pervasives_Native.None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10958
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2
                          in
                       let guard =
                         let uu____10965 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives_Native.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10965  in
                       let wl1 =
                         solve_prob orig (FStar_Pervasives_Native.Some guard)
                           [] wl
                          in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10975 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10975 with
                        | (occurs_ok,uu____10984) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10989 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10989
                            then
                              let sol =
                                let uu____10991 =
                                  let uu____10996 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10996)  in
                                TERM uu____10991  in
                              let wl1 =
                                solve_prob orig FStar_Pervasives_Native.None
                                  [sol] wl
                                 in
                              solve env wl1
                            else
                              (let uu____11009 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____11009
                               then
                                 let uu____11010 =
                                   force_quasi_pattern
                                     (FStar_Pervasives_Native.Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____11010 with
                                 | (sol,(uu____11024,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____11034 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____11034
                                       then
                                         let uu____11035 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____11035
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11040 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____11042 = lhs  in
             match uu____11042 with
             | (t1,u1,k1,args1) ->
                 let uu____11047 = rhs  in
                 (match uu____11047 with
                  | (t2,u2,k2,args2) ->
                      let maybe_pat_vars1 = pat_vars env [] args1  in
                      let maybe_pat_vars2 = pat_vars env [] args2  in
                      let r = t2.FStar_Syntax_Syntax.pos  in
                      (match (maybe_pat_vars1, maybe_pat_vars2) with
                       | (FStar_Pervasives_Native.Some
                          xs,FStar_Pervasives_Native.Some ys) ->
                           solve_both_pats wl (u1, k1, xs, args1)
                             (u2, k2, ys, args2) t2.FStar_Syntax_Syntax.pos
                       | (FStar_Pervasives_Native.Some
                          xs,FStar_Pervasives_Native.None ) ->
                           solve_one_pat (t1, u1, k1, xs) rhs
                       | (FStar_Pervasives_Native.None
                          ,FStar_Pervasives_Native.Some ys) ->
                           solve_one_pat (t2, u2, k2, ys) lhs
                       | uu____11073 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11079 =
                                force_quasi_pattern
                                  FStar_Pervasives_Native.None
                                  (t1, u1, k1, args1)
                                 in
                              match uu____11079 with
                              | (sol,uu____11086) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____11089 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____11089
                                    then
                                      let uu____11090 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11090
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11095 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____11097 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____11097
        then
          let uu____11098 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____11098
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____11102 = FStar_Util.physical_equality t1 t2  in
           if uu____11102
           then
             let uu____11103 =
               solve_prob orig FStar_Pervasives_Native.None [] wl  in
             solve env uu____11103
           else
             ((let uu____11106 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____11106
               then
                 let uu____11107 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____11107
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_ascribed uu____11110,uu____11111) ->
                   let uu____11129 =
                     let uu___164_11130 = problem  in
                     let uu____11131 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_11130.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____11131;
                       FStar_TypeChecker_Common.relation =
                         (uu___164_11130.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___164_11130.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___164_11130.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_11130.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___164_11130.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_11130.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_11130.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_11130.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11129 wl
               | (FStar_Syntax_Syntax.Tm_meta uu____11132,uu____11133) ->
                   let uu____11138 =
                     let uu___164_11139 = problem  in
                     let uu____11140 = FStar_Syntax_Util.unmeta t1  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___164_11139.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = uu____11140;
                       FStar_TypeChecker_Common.relation =
                         (uu___164_11139.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___164_11139.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___164_11139.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___164_11139.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___164_11139.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___164_11139.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___164_11139.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___164_11139.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11138 wl
               | (uu____11141,FStar_Syntax_Syntax.Tm_ascribed uu____11142) ->
                   let uu____11160 =
                     let uu___165_11161 = problem  in
                     let uu____11162 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_11161.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_11161.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___165_11161.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____11162;
                       FStar_TypeChecker_Common.element =
                         (uu___165_11161.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_11161.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___165_11161.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_11161.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_11161.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_11161.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11160 wl
               | (uu____11163,FStar_Syntax_Syntax.Tm_meta uu____11164) ->
                   let uu____11169 =
                     let uu___165_11170 = problem  in
                     let uu____11171 = FStar_Syntax_Util.unmeta t2  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___165_11170.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___165_11170.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___165_11170.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = uu____11171;
                       FStar_TypeChecker_Common.element =
                         (uu___165_11170.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___165_11170.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.scope =
                         (uu___165_11170.FStar_TypeChecker_Common.scope);
                       FStar_TypeChecker_Common.reason =
                         (uu___165_11170.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___165_11170.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___165_11170.FStar_TypeChecker_Common.rank)
                     }  in
                   solve_t' env uu____11169 wl
               | (FStar_Syntax_Syntax.Tm_bvar uu____11172,uu____11173) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11174,FStar_Syntax_Syntax.Tm_bvar uu____11175) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11215 =
                     match uu___130_11215 with
                     | [] -> c
                     | bs ->
                         let uu____11229 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                             FStar_Pervasives_Native.None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____11229
                      in
                   let uu____11239 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____11239 with
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
                                   let uu____11325 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____11325
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____11327 =
                                   mk_problem scope orig c12 rel c22
                                     FStar_Pervasives_Native.None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11327))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11404 =
                     match uu___131_11404 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                           FStar_Pervasives_Native.None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____11439 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____11439 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11522 =
                                   let uu____11525 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____11526 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____11525
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11526 FStar_Pervasives_Native.None
                                     "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11522))
               | (FStar_Syntax_Syntax.Tm_abs uu____11529,uu____11530) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11553 -> true
                     | uu____11568 -> false  in
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
                   let uu____11596 =
                     let uu____11607 = maybe_eta t1  in
                     let uu____11612 = maybe_eta t2  in
                     (uu____11607, uu____11612)  in
                   (match uu____11596 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11643 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11643.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11643.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11643.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11643.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11643.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11643.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11643.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11643.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11662 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11662
                        then
                          let uu____11663 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11663 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11684 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11684
                        then
                          let uu____11685 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11685 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11690 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11701,FStar_Syntax_Syntax.Tm_abs uu____11702) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11725 -> true
                     | uu____11740 -> false  in
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
                   let uu____11768 =
                     let uu____11779 = maybe_eta t1  in
                     let uu____11784 = maybe_eta t2  in
                     (uu____11779, uu____11784)  in
                   (match uu____11768 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___166_11815 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___166_11815.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___166_11815.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___166_11815.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___166_11815.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___166_11815.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___166_11815.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___166_11815.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___166_11815.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11834 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11834
                        then
                          let uu____11835 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11835 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11856 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11856
                        then
                          let uu____11857 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11857 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11862 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11873,FStar_Syntax_Syntax.Tm_refine uu____11874) ->
                   let uu____11883 = as_refinement env wl t1  in
                   (match uu____11883 with
                    | (x1,phi1) ->
                        let uu____11888 = as_refinement env wl t2  in
                        (match uu____11888 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11894 =
                                 mk_problem (p_scope orig) orig
                                   x1.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.relation
                                   x2.FStar_Syntax_Syntax.sort
                                   problem.FStar_TypeChecker_Common.element
                                   "refinement base type"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_63  ->
                                    FStar_TypeChecker_Common.TProb _0_63)
                                 uu____11894
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
                               let uu____11927 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____11927
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____11931 =
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
                                 let uu____11937 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____11937 impl
                                  in
                               let wl1 =
                                 solve_prob orig
                                   (FStar_Pervasives_Native.Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11944 =
                                   let uu____11947 =
                                     let uu____11948 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____11948 :: (p_scope orig)  in
                                   mk_problem uu____11947 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21
                                     FStar_Pervasives_Native.None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11944
                                  in
                               let uu____11951 =
                                 solve env1
                                   (let uu___167_11952 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___167_11952.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___167_11952.smt_ok);
                                      tcenv = (uu___167_11952.tcenv)
                                    })
                                  in
                               (match uu____11951 with
                                | Failed uu____11956 -> fallback ()
                                | Success uu____11959 ->
                                    let guard =
                                      let uu____11963 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives_Native.fst
                                         in
                                      let uu____11966 =
                                        let uu____11967 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____11967
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____11963
                                        uu____11966
                                       in
                                    let wl1 =
                                      solve_prob orig
                                        (FStar_Pervasives_Native.Some guard)
                                        [] wl
                                       in
                                    let wl2 =
                                      let uu___168_11974 = wl1  in
                                      {
                                        attempting =
                                          (uu___168_11974.attempting);
                                        wl_deferred =
                                          (uu___168_11974.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___168_11974.defer_ok);
                                        smt_ok = (uu___168_11974.smt_ok);
                                        tcenv = (uu___168_11974.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11976,FStar_Syntax_Syntax.Tm_uvar uu____11977) ->
                   let uu____11994 = destruct_flex_t t1  in
                   let uu____11995 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11994 uu____11995
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11996;
                     FStar_Syntax_Syntax.tk = uu____11997;
                     FStar_Syntax_Syntax.pos = uu____11998;
                     FStar_Syntax_Syntax.vars = uu____11999;_},uu____12000),FStar_Syntax_Syntax.Tm_uvar
                  uu____12001) ->
                   let uu____12032 = destruct_flex_t t1  in
                   let uu____12033 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12032 uu____12033
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12034,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12035;
                     FStar_Syntax_Syntax.tk = uu____12036;
                     FStar_Syntax_Syntax.pos = uu____12037;
                     FStar_Syntax_Syntax.vars = uu____12038;_},uu____12039))
                   ->
                   let uu____12070 = destruct_flex_t t1  in
                   let uu____12071 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12070 uu____12071
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12072;
                     FStar_Syntax_Syntax.tk = uu____12073;
                     FStar_Syntax_Syntax.pos = uu____12074;
                     FStar_Syntax_Syntax.vars = uu____12075;_},uu____12076),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12077;
                     FStar_Syntax_Syntax.tk = uu____12078;
                     FStar_Syntax_Syntax.pos = uu____12079;
                     FStar_Syntax_Syntax.vars = uu____12080;_},uu____12081))
                   ->
                   let uu____12126 = destruct_flex_t t1  in
                   let uu____12127 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12126 uu____12127
               | (FStar_Syntax_Syntax.Tm_uvar uu____12128,uu____12129) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12138 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12138 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12142;
                     FStar_Syntax_Syntax.tk = uu____12143;
                     FStar_Syntax_Syntax.pos = uu____12144;
                     FStar_Syntax_Syntax.vars = uu____12145;_},uu____12146),uu____12147)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12170 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12170 t2 wl
               | (uu____12174,FStar_Syntax_Syntax.Tm_uvar uu____12175) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12184,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12185;
                     FStar_Syntax_Syntax.tk = uu____12186;
                     FStar_Syntax_Syntax.pos = uu____12187;
                     FStar_Syntax_Syntax.vars = uu____12188;_},uu____12189))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12212,FStar_Syntax_Syntax.Tm_type uu____12213) ->
                   solve_t' env
                     (let uu___169_12222 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12222.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12222.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12222.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12222.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12222.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12222.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12222.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12222.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12222.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12223;
                     FStar_Syntax_Syntax.tk = uu____12224;
                     FStar_Syntax_Syntax.pos = uu____12225;
                     FStar_Syntax_Syntax.vars = uu____12226;_},uu____12227),FStar_Syntax_Syntax.Tm_type
                  uu____12228) ->
                   solve_t' env
                     (let uu___169_12251 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12251.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12251.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12251.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12251.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12251.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12251.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12251.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12251.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12251.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12252,FStar_Syntax_Syntax.Tm_arrow uu____12253) ->
                   solve_t' env
                     (let uu___169_12269 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12269.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12269.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12269.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12269.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12269.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12269.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12269.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12269.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12269.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12270;
                     FStar_Syntax_Syntax.tk = uu____12271;
                     FStar_Syntax_Syntax.pos = uu____12272;
                     FStar_Syntax_Syntax.vars = uu____12273;_},uu____12274),FStar_Syntax_Syntax.Tm_arrow
                  uu____12275) ->
                   solve_t' env
                     (let uu___169_12305 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___169_12305.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___169_12305.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___169_12305.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___169_12305.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___169_12305.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___169_12305.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___169_12305.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___169_12305.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___169_12305.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12306,uu____12307) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12318 =
                        let uu____12319 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12319  in
                      if uu____12318
                      then
                        let uu____12320 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___170_12323 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12323.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12323.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12323.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12323.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12323.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12323.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12323.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12323.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12323.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12324 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12320 uu____12324 t2
                          wl
                      else
                        (let uu____12329 = base_and_refinement env wl t2  in
                         match uu____12329 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12359 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___171_12362 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12362.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12362.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12362.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12362.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12362.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12362.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12362.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12362.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12362.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12363 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12359
                                    uu____12363 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12378 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12378.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12378.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12381 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_67  ->
                                         FStar_TypeChecker_Common.TProb _0_67)
                                      uu____12381
                                     in
                                  let guard =
                                    let uu____12389 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12389
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12395;
                     FStar_Syntax_Syntax.tk = uu____12396;
                     FStar_Syntax_Syntax.pos = uu____12397;
                     FStar_Syntax_Syntax.vars = uu____12398;_},uu____12399),uu____12400)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12425 =
                        let uu____12426 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12426  in
                      if uu____12425
                      then
                        let uu____12427 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___170_12430 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___170_12430.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___170_12430.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___170_12430.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___170_12430.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___170_12430.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___170_12430.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___170_12430.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___170_12430.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___170_12430.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12431 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12427 uu____12431 t2
                          wl
                      else
                        (let uu____12436 = base_and_refinement env wl t2  in
                         match uu____12436 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | FStar_Pervasives_Native.None  ->
                                  let uu____12466 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___171_12469 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___171_12469.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___171_12469.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___171_12469.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___171_12469.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___171_12469.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___171_12469.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___171_12469.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___171_12469.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___171_12469.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12470 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12466
                                    uu____12470 t_base wl
                              | FStar_Pervasives_Native.Some (y,phi) ->
                                  let y' =
                                    let uu___172_12485 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___172_12485.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___172_12485.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12488 =
                                      mk_problem
                                        problem.FStar_TypeChecker_Common.scope
                                        orig t1 new_rel
                                        y.FStar_Syntax_Syntax.sort
                                        problem.FStar_TypeChecker_Common.element
                                        "flex-rigid: base type"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_70  ->
                                         FStar_TypeChecker_Common.TProb _0_70)
                                      uu____12488
                                     in
                                  let guard =
                                    let uu____12496 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12496
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig
                                      (FStar_Pervasives_Native.Some guard) []
                                      wl
                                     in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12502,FStar_Syntax_Syntax.Tm_uvar uu____12503) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12513 = base_and_refinement env wl t1  in
                      match uu____12513 with
                      | (t_base,uu____12524) ->
                          solve_t env
                            (let uu___173_12539 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12539.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12539.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12539.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12539.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12539.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12539.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12539.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12539.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12542,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12543;
                     FStar_Syntax_Syntax.tk = uu____12544;
                     FStar_Syntax_Syntax.pos = uu____12545;
                     FStar_Syntax_Syntax.vars = uu____12546;_},uu____12547))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12571 = base_and_refinement env wl t1  in
                      match uu____12571 with
                      | (t_base,uu____12582) ->
                          solve_t env
                            (let uu___173_12597 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___173_12597.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___173_12597.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___173_12597.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___173_12597.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___173_12597.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___173_12597.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___173_12597.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___173_12597.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12600,uu____12601) ->
                   let t21 =
                     let uu____12609 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____12609  in
                   solve_t env
                     (let uu___174_12622 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_12622.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___174_12622.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___174_12622.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___174_12622.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_12622.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_12622.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_12622.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_12622.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_12622.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12623,FStar_Syntax_Syntax.Tm_refine uu____12624) ->
                   let t11 =
                     let uu____12632 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____12632  in
                   solve_t env
                     (let uu___175_12645 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_12645.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___175_12645.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___175_12645.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___175_12645.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_12645.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_12645.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_12645.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_12645.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_12645.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12648,uu____12649) ->
                   let head1 =
                     let uu____12668 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12668
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12699 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12699
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12727 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12727
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12736 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12736
                      then
                        let guard =
                          let uu____12743 =
                            let uu____12744 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12744 = FStar_Syntax_Util.Equal  in
                          if uu____12743
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12747 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_71  ->
                                  FStar_Pervasives_Native.Some _0_71)
                               uu____12747)
                           in
                        let uu____12749 = solve_prob orig guard [] wl  in
                        solve env uu____12749
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12752,uu____12753) ->
                   let head1 =
                     let uu____12761 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12761
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12792 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12792
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12820 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12820
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12829 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12829
                      then
                        let guard =
                          let uu____12836 =
                            let uu____12837 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12837 = FStar_Syntax_Util.Equal  in
                          if uu____12836
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12840 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_72  ->
                                  FStar_Pervasives_Native.Some _0_72)
                               uu____12840)
                           in
                        let uu____12842 = solve_prob orig guard [] wl  in
                        solve env uu____12842
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12845,uu____12846) ->
                   let head1 =
                     let uu____12850 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12850
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12881 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12881
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12909 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12909
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12918 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12918
                      then
                        let guard =
                          let uu____12925 =
                            let uu____12926 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12926 = FStar_Syntax_Util.Equal  in
                          if uu____12925
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____12929 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_73  ->
                                  FStar_Pervasives_Native.Some _0_73)
                               uu____12929)
                           in
                        let uu____12931 = solve_prob orig guard [] wl  in
                        solve env uu____12931
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12934,uu____12935) ->
                   let head1 =
                     let uu____12939 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12939
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____12970 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12970
                       FStar_Pervasives_Native.fst
                      in
                   let uu____12998 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12998
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13007 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13007
                      then
                        let guard =
                          let uu____13014 =
                            let uu____13015 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13015 = FStar_Syntax_Util.Equal  in
                          if uu____13014
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13018 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_74  ->
                                  FStar_Pervasives_Native.Some _0_74)
                               uu____13018)
                           in
                        let uu____13020 = solve_prob orig guard [] wl  in
                        solve env uu____13020
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____13023,uu____13024) ->
                   let head1 =
                     let uu____13028 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13028
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13059 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13059
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13087 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13087
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13096 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13096
                      then
                        let guard =
                          let uu____13103 =
                            let uu____13104 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13104 = FStar_Syntax_Util.Equal  in
                          if uu____13103
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13107 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_75  ->
                                  FStar_Pervasives_Native.Some _0_75)
                               uu____13107)
                           in
                        let uu____13109 = solve_prob orig guard [] wl  in
                        solve env uu____13109
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13112,uu____13113) ->
                   let head1 =
                     let uu____13126 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13126
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13157 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13157
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13185 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13185
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13194 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13194
                      then
                        let guard =
                          let uu____13201 =
                            let uu____13202 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13202 = FStar_Syntax_Util.Equal  in
                          if uu____13201
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13205 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_76  ->
                                  FStar_Pervasives_Native.Some _0_76)
                               uu____13205)
                           in
                        let uu____13207 = solve_prob orig guard [] wl  in
                        solve env uu____13207
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13210,FStar_Syntax_Syntax.Tm_match uu____13211) ->
                   let head1 =
                     let uu____13230 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13230
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13261 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13261
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13289 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13289
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13298 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13298
                      then
                        let guard =
                          let uu____13305 =
                            let uu____13306 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13306 = FStar_Syntax_Util.Equal  in
                          if uu____13305
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13309 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_77  ->
                                  FStar_Pervasives_Native.Some _0_77)
                               uu____13309)
                           in
                        let uu____13311 = solve_prob orig guard [] wl  in
                        solve env uu____13311
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13314,FStar_Syntax_Syntax.Tm_uinst uu____13315) ->
                   let head1 =
                     let uu____13323 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13323
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13354 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13354
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13382 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13382
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13391 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13391
                      then
                        let guard =
                          let uu____13398 =
                            let uu____13399 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13399 = FStar_Syntax_Util.Equal  in
                          if uu____13398
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13402 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_78  ->
                                  FStar_Pervasives_Native.Some _0_78)
                               uu____13402)
                           in
                        let uu____13404 = solve_prob orig guard [] wl  in
                        solve env uu____13404
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13407,FStar_Syntax_Syntax.Tm_name uu____13408) ->
                   let head1 =
                     let uu____13412 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13412
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13443 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13443
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13471 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13471
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13480 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13480
                      then
                        let guard =
                          let uu____13487 =
                            let uu____13488 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13488 = FStar_Syntax_Util.Equal  in
                          if uu____13487
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13491 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_79  ->
                                  FStar_Pervasives_Native.Some _0_79)
                               uu____13491)
                           in
                        let uu____13493 = solve_prob orig guard [] wl  in
                        solve env uu____13493
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13496,FStar_Syntax_Syntax.Tm_constant uu____13497) ->
                   let head1 =
                     let uu____13501 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13501
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13532 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13532
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13560 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13560
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13569 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13569
                      then
                        let guard =
                          let uu____13576 =
                            let uu____13577 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13577 = FStar_Syntax_Util.Equal  in
                          if uu____13576
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13580 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_80  ->
                                  FStar_Pervasives_Native.Some _0_80)
                               uu____13580)
                           in
                        let uu____13582 = solve_prob orig guard [] wl  in
                        solve env uu____13582
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13585,FStar_Syntax_Syntax.Tm_fvar uu____13586) ->
                   let head1 =
                     let uu____13590 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13590
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13621 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13621
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13649 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13649
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13658 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13658
                      then
                        let guard =
                          let uu____13665 =
                            let uu____13666 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13666 = FStar_Syntax_Util.Equal  in
                          if uu____13665
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13669 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_81  ->
                                  FStar_Pervasives_Native.Some _0_81)
                               uu____13669)
                           in
                        let uu____13671 = solve_prob orig guard [] wl  in
                        solve env uu____13671
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13674,FStar_Syntax_Syntax.Tm_app uu____13675) ->
                   let head1 =
                     let uu____13688 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13688
                       FStar_Pervasives_Native.fst
                      in
                   let head2 =
                     let uu____13719 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13719
                       FStar_Pervasives_Native.fst
                      in
                   let uu____13747 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13747
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13756 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13756
                      then
                        let guard =
                          let uu____13763 =
                            let uu____13764 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13764 = FStar_Syntax_Util.Equal  in
                          if uu____13763
                          then FStar_Pervasives_Native.None
                          else
                            (let uu____13767 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left
                               (fun _0_82  ->
                                  FStar_Pervasives_Native.Some _0_82)
                               uu____13767)
                           in
                        let uu____13769 = solve_prob orig guard [] wl  in
                        solve env uu____13769
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_let uu____13772,uu____13773) ->
                   let uu____13781 =
                     let uu____13782 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13783 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13782
                       uu____13783
                      in
                   failwith uu____13781
               | (FStar_Syntax_Syntax.Tm_delayed uu____13784,uu____13785) ->
                   let uu____13806 =
                     let uu____13807 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13808 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13807
                       uu____13808
                      in
                   failwith uu____13806
               | (uu____13809,FStar_Syntax_Syntax.Tm_delayed uu____13810) ->
                   let uu____13831 =
                     let uu____13832 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13833 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13832
                       uu____13833
                      in
                   failwith uu____13831
               | (uu____13834,FStar_Syntax_Syntax.Tm_let uu____13835) ->
                   let uu____13843 =
                     let uu____13844 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13845 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13844
                       uu____13845
                      in
                   failwith uu____13843
               | uu____13846 -> giveup env "head tag mismatch" orig)))

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
          mk_problem (p_scope orig) orig t1 rel t2
            FStar_Pervasives_Native.None reason
           in
        let solve_eq c1_comp c2_comp =
          (let uu____13878 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____13878
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13886  ->
                  fun uu____13887  ->
                    match (uu____13886, uu____13887) with
                    | ((a1,uu____13897),(a2,uu____13899)) ->
                        let uu____13904 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13904)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____13910 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p)
                      FStar_Pervasives_Native.fst) sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____13910  in
           let wl1 =
             solve_prob orig (FStar_Pervasives_Native.Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____13930 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13937)::[] -> wp1
              | uu____13950 ->
                  let uu____13956 =
                    let uu____13957 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13957
                     in
                  failwith uu____13956
               in
            let uu____13960 =
              let uu____13966 =
                let uu____13967 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____13967  in
              [uu____13966]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13960;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13968 = lift_c1 ()  in solve_eq uu____13968 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13972  ->
                       match uu___132_13972 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13973 -> false))
                in
             let uu____13974 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13998)::uu____13999,(wp2,uu____14001)::uu____14002)
                   -> (wp1, wp2)
               | uu____14043 ->
                   let uu____14056 =
                     let uu____14057 =
                       let uu____14060 =
                         let uu____14061 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____14062 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14061 uu____14062
                          in
                       (uu____14060, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____14057  in
                   raise uu____14056
                in
             match uu____13974 with
             | (wpc1,wpc2) ->
                 let uu____14079 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____14079
                 then
                   let uu____14082 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ
                       FStar_Pervasives_Native.None "result type"
                      in
                   solve_t env uu____14082 wl
                 else
                   (let uu____14086 =
                      let uu____14090 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____14090  in
                    match uu____14086 with
                    | (c2_decl,qualifiers) ->
                        let uu____14102 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____14102
                        then
                          let c1_repr =
                            let uu____14105 =
                              let uu____14106 =
                                let uu____14107 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____14107  in
                              let uu____14108 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14106 uu____14108
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14105
                             in
                          let c2_repr =
                            let uu____14110 =
                              let uu____14111 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____14112 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14111 uu____14112
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14110
                             in
                          let prob =
                            let uu____14114 =
                              let uu____14117 =
                                let uu____14118 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____14119 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14118
                                  uu____14119
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14117
                               in
                            FStar_TypeChecker_Common.TProb uu____14114  in
                          let wl1 =
                            let uu____14121 =
                              let uu____14123 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_Pervasives_Native.Some uu____14123  in
                            solve_prob orig uu____14121 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14130 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____14130
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14132 =
                                     let uu____14135 =
                                       let uu____14136 =
                                         let uu____14146 =
                                           let uu____14147 =
                                             let uu____14148 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ
                                                in
                                             [uu____14148]  in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14147 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____14149 =
                                           let uu____14151 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____14152 =
                                             let uu____14154 =
                                               let uu____14155 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14155
                                                in
                                             [uu____14154]  in
                                           uu____14151 :: uu____14152  in
                                         (uu____14146, uu____14149)  in
                                       FStar_Syntax_Syntax.Tm_app uu____14136
                                        in
                                     FStar_Syntax_Syntax.mk uu____14135  in
                                   uu____14132
                                     (FStar_Pervasives_Native.Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14166 =
                                    let uu____14169 =
                                      let uu____14170 =
                                        let uu____14180 =
                                          let uu____14181 =
                                            let uu____14182 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____14182]  in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14181 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____14183 =
                                          let uu____14185 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____14186 =
                                            let uu____14188 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____14189 =
                                              let uu____14191 =
                                                let uu____14192 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14192
                                                 in
                                              [uu____14191]  in
                                            uu____14188 :: uu____14189  in
                                          uu____14185 :: uu____14186  in
                                        (uu____14180, uu____14183)  in
                                      FStar_Syntax_Syntax.Tm_app uu____14170
                                       in
                                    FStar_Syntax_Syntax.mk uu____14169  in
                                  uu____14166
                                    (FStar_Pervasives_Native.Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r)
                              in
                           let base_prob =
                             let uu____14203 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14203
                              in
                           let wl1 =
                             let uu____14209 =
                               let uu____14211 =
                                 let uu____14214 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____14214 g  in
                               FStar_All.pipe_left
                                 (fun _0_85  ->
                                    FStar_Pervasives_Native.Some _0_85)
                                 uu____14211
                                in
                             solve_prob orig uu____14209 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____14224 = FStar_Util.physical_equality c1 c2  in
        if uu____14224
        then
          let uu____14225 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____14225
        else
          ((let uu____14228 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____14228
            then
              let uu____14229 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____14230 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14229
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14230
            else ());
           (let uu____14232 =
              let uu____14235 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____14236 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____14235, uu____14236)  in
            match uu____14232 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14240),FStar_Syntax_Syntax.Total
                    (t2,uu____14242)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14255 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14255 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14258,FStar_Syntax_Syntax.Total uu____14259) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14271),FStar_Syntax_Syntax.Total
                    (t2,uu____14273)) ->
                     let uu____14286 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14286 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14290),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14292)) ->
                     let uu____14305 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14305 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14309),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14311)) ->
                     let uu____14324 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____14324 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14327,FStar_Syntax_Syntax.Comp uu____14328) ->
                     let uu____14334 =
                       let uu___176_14337 = problem  in
                       let uu____14340 =
                         let uu____14341 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14341
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14337.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14340;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14337.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14337.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14337.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14337.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14337.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14337.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14337.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14337.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14334 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14342,FStar_Syntax_Syntax.Comp uu____14343) ->
                     let uu____14349 =
                       let uu___176_14352 = problem  in
                       let uu____14355 =
                         let uu____14356 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14356
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14352.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14355;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14352.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14352.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14352.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14352.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14352.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14352.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14352.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14352.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14349 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14357,FStar_Syntax_Syntax.GTotal uu____14358) ->
                     let uu____14364 =
                       let uu___177_14367 = problem  in
                       let uu____14370 =
                         let uu____14371 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14371
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14367.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14367.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14367.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14370;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14367.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14367.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14367.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14367.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14367.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14367.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14364 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14372,FStar_Syntax_Syntax.Total uu____14373) ->
                     let uu____14379 =
                       let uu___177_14382 = problem  in
                       let uu____14385 =
                         let uu____14386 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14386
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14382.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14382.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14382.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14385;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14382.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14382.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14382.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14382.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14382.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14382.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14379 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14387,FStar_Syntax_Syntax.Comp uu____14388) ->
                     let uu____14389 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____14389
                     then
                       let uu____14390 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____14390 wl
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
                           (let uu____14400 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14400
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14402 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____14402 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____14404 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14405 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____14405)
                                   in
                                if uu____14404
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
                                  (let uu____14408 =
                                     let uu____14409 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____14410 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14409 uu____14410
                                      in
                                   giveup env uu____14408 orig)
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14415 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14435  ->
              match uu____14435 with
              | (uu____14446,uu____14447,u,uu____14449,uu____14450,uu____14451)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____14415 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                             FStar_Syntax_Syntax.universe)
                                             FStar_Pervasives_Native.tuple2
                                             Prims.list)
    FStar_Pervasives_Native.tuple2 -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14480 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____14480 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____14490 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____14502  ->
                match uu____14502 with
                | (u1,u2) ->
                    let uu____14507 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____14508 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____14507 uu____14508))
         in
      FStar_All.pipe_right uu____14490 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14520,[])) -> "{}"
      | uu____14533 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14543 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____14543
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____14546 =
              FStar_List.map
                (fun uu____14550  ->
                   match uu____14550 with
                   | (uu____14553,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____14546 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____14557 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14557 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14595 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____14595
    then
      let uu____14596 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____14597 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14596
        (rel_to_string rel) uu____14597
    else "TOP"  in
  let p = new_problem env lhs rel rhs elt loc reason  in p 
let new_t_prob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_TypeChecker_Common.rel ->
        FStar_Syntax_Syntax.term ->
          (FStar_TypeChecker_Common.prob,FStar_Syntax_Syntax.bv)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun t1  ->
      fun rel  ->
        fun t2  ->
          let x =
            let uu____14617 =
              let uu____14619 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left
                (fun _0_86  -> FStar_Pervasives_Native.Some _0_86)
                uu____14619
               in
            FStar_Syntax_Syntax.new_bv uu____14617 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____14625 =
              let uu____14627 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left
                (fun _0_87  -> FStar_Pervasives_Native.Some _0_87)
                uu____14627
               in
            let uu____14629 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____14625 uu____14629  in
          ((FStar_TypeChecker_Common.TProb p), x)
  
let solve_and_commit :
  FStar_TypeChecker_Env.env ->
    worklist ->
      ((FStar_TypeChecker_Common.prob,Prims.string)
         FStar_Pervasives_Native.tuple2 ->
         FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option)
        -> FStar_TypeChecker_Common.deferred FStar_Pervasives_Native.option
  =
  fun env  ->
    fun probs  ->
      fun err1  ->
        let probs1 =
          let uu____14652 = FStar_Options.eager_inference ()  in
          if uu____14652
          then
            let uu___178_14653 = probs  in
            {
              attempting = (uu___178_14653.attempting);
              wl_deferred = (uu___178_14653.wl_deferred);
              ctr = (uu___178_14653.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14653.smt_ok);
              tcenv = (uu___178_14653.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred ->
            (FStar_Unionfind.commit tx; FStar_Pervasives_Native.Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14664 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____14664
              then
                let uu____14665 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____14665
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
          ((let uu____14675 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____14675
            then
              let uu____14676 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14676
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____14680 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____14680
             then
               let uu____14681 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14681
             else ());
            (let f2 =
               let uu____14684 =
                 let uu____14685 = FStar_Syntax_Util.unmeta f1  in
                 uu____14685.FStar_Syntax_Syntax.n  in
               match uu____14684 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14689 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___179_14690 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14690.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14690.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14690.FStar_TypeChecker_Env.implicits)
             })))
  
let with_guard :
  FStar_TypeChecker_Env.env ->
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
            let uu____14705 =
              let uu____14706 =
                let uu____14707 =
                  let uu____14708 =
                    FStar_All.pipe_right (p_guard prob)
                      FStar_Pervasives_Native.fst
                     in
                  FStar_All.pipe_right uu____14708
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14707;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____14706  in
            FStar_All.pipe_left
              (fun _0_89  -> FStar_Pervasives_Native.Some _0_89) uu____14705
  
let with_guard_no_simp env prob dopt =
  match dopt with
  | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some d ->
      let uu____14741 =
        let uu____14742 =
          let uu____14743 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives_Native.fst
             in
          FStar_All.pipe_right uu____14743
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90)
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____14742;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        }  in
      FStar_Pervasives_Native.Some uu____14741
  
let try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____14769 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14769
           then
             let uu____14770 = FStar_Syntax_Print.term_to_string t1  in
             let uu____14771 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14770
               uu____14771
           else ());
          (let prob =
             let uu____14774 =
               let uu____14777 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2
                 FStar_Pervasives_Native.None uu____14777
                in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14774
              in
           let g =
             let uu____14782 =
               let uu____14784 = singleton' env prob smt_ok  in
               solve_and_commit env uu____14784
                 (fun uu____14785  -> FStar_Pervasives_Native.None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____14782  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14799 = try_teq true env t1 t2  in
        match uu____14799 with
        | FStar_Pervasives_Native.None  ->
            let uu____14801 =
              let uu____14802 =
                let uu____14805 =
                  FStar_TypeChecker_Err.basic_type_error env
                    FStar_Pervasives_Native.None t2 t1
                   in
                let uu____14806 = FStar_TypeChecker_Env.get_range env  in
                (uu____14805, uu____14806)  in
              FStar_Errors.Error uu____14802  in
            raise uu____14801
        | FStar_Pervasives_Native.Some g ->
            ((let uu____14809 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____14809
              then
                let uu____14810 = FStar_Syntax_Print.term_to_string t1  in
                let uu____14811 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14812 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14810
                  uu____14811 uu____14812
              else ());
             g)
  
let try_subtype' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun smt_ok  ->
          (let uu____14828 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14828
           then
             let uu____14829 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____14830 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14829
               uu____14830
           else ());
          (let uu____14832 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____14832 with
           | (prob,x) ->
               let g =
                 let uu____14840 =
                   let uu____14842 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____14842
                     (fun uu____14843  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____14840  in
               ((let uu____14849 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____14849
                 then
                   let uu____14850 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____14851 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____14852 =
                     let uu____14853 = FStar_Util.must g  in
                     guard_to_string env uu____14853  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14850 uu____14851 uu____14852
                 else ());
                abstract_guard x g))
  
let try_subtype :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
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
          let uu____14877 = FStar_TypeChecker_Env.get_range env  in
          let uu____14878 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.err uu____14877 uu____14878
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14890 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____14890
         then
           let uu____14891 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____14892 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14891
             uu____14892
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____14897 =
             let uu____14900 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 FStar_Pervasives_Native.None
               uu____14900 "sub_comp"
              in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14897
            in
         let uu____14903 =
           let uu____14905 = singleton env prob  in
           solve_and_commit env uu____14905
             (fun uu____14906  -> FStar_Pervasives_Native.None)
            in
         FStar_All.pipe_left (with_guard env prob) uu____14903)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                                 FStar_Syntax_Syntax.universe)
                                                 FStar_Pervasives_Native.tuple2
                                                 Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14925  ->
        match uu____14925 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14950 =
                 let uu____14951 =
                   let uu____14954 =
                     let uu____14955 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____14956 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14955 uu____14956
                      in
                   let uu____14957 = FStar_TypeChecker_Env.get_range env  in
                   (uu____14954, uu____14957)  in
                 FStar_Errors.Error uu____14951  in
               raise uu____14950)
               in
            let equiv v1 v' =
              let uu____14965 =
                let uu____14968 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____14969 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____14968, uu____14969)  in
              match uu____14965 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14977 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14991 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____14991 with
                      | FStar_Syntax_Syntax.U_unif uu____14995 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____15006  ->
                                    match uu____15006 with
                                    | (u,v') ->
                                        let uu____15012 = equiv v1 v'  in
                                        if uu____15012
                                        then
                                          let uu____15014 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____15014 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____15024 -> []))
               in
            let uu____15027 =
              let wl =
                let uu___180_15030 = empty_worklist env  in
                {
                  attempting = (uu___180_15030.attempting);
                  wl_deferred = (uu___180_15030.wl_deferred);
                  ctr = (uu___180_15030.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_15030.smt_ok);
                  tcenv = (uu___180_15030.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15037  ->
                      match uu____15037 with
                      | (lb,v1) ->
                          let uu____15042 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____15042 with
                           | USolved wl1 -> ()
                           | uu____15044 -> fail lb v1)))
               in
            let rec check_ineq uu____15050 =
              match uu____15050 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15057) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Unionfind.equivalent u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____15069,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15071,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15076) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15080,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15085 -> false)
               in
            let uu____15088 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15094  ->
                      match uu____15094 with
                      | (u,v1) ->
                          let uu____15099 = check_ineq (u, v1)  in
                          if uu____15099
                          then true
                          else
                            ((let uu____15102 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____15102
                              then
                                let uu____15103 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____15104 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____15103
                                  uu____15104
                              else ());
                             false)))
               in
            if uu____15088
            then ()
            else
              ((let uu____15108 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____15108
                then
                  ((let uu____15110 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15110);
                   FStar_Unionfind.rollback tx;
                   (let uu____15116 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15116))
                else ());
               (let uu____15122 =
                  let uu____15123 =
                    let uu____15126 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15126)
                     in
                  FStar_Errors.Error uu____15123  in
                raise uu____15122))
  
let solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list,(FStar_Syntax_Syntax.universe,
                                               FStar_Syntax_Syntax.universe)
                                               FStar_Pervasives_Native.tuple2
                                               Prims.list)
      FStar_Pervasives_Native.tuple2 -> Prims.unit
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
      let fail uu____15159 =
        match uu____15159 with
        | (d,s) ->
            let msg = explain env d s  in
            raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____15169 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____15169
       then
         let uu____15170 = wl_to_string wl  in
         let uu____15171 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15170 uu____15171
       else ());
      (let g1 =
         let uu____15183 = solve_and_commit env wl fail  in
         match uu____15183 with
         | FStar_Pervasives_Native.Some [] ->
             let uu___181_15190 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15190.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15190.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15190.FStar_TypeChecker_Env.implicits)
             }
         | uu____15193 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15196 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15196.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15196.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15196.FStar_TypeChecker_Env.implicits)
        }))
  
let discharge_guard' :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Env.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Env.guard_t FStar_Pervasives_Native.option
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let g1 = solve_deferred_constraints env g  in
          let ret_g =
            let uu___183_15222 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15222.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15222.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15222.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____15223 =
            let uu____15224 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____15224  in
          if uu____15223
          then FStar_Pervasives_Native.Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  ->
                 FStar_Pervasives_Native.Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15230 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery"))
                      in
                   if uu____15230
                   then
                     let uu____15231 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____15232 =
                       let uu____15233 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15233
                        in
                     FStar_Errors.diag uu____15231 uu____15232
                   else ());
                  (let vc1 =
                     FStar_TypeChecker_Normalize.normalize
                       [FStar_TypeChecker_Normalize.Eager_unfolding;
                       FStar_TypeChecker_Normalize.Beta;
                       FStar_TypeChecker_Normalize.Simplify] env vc
                      in
                   match check_trivial vc1 with
                   | FStar_TypeChecker_Common.Trivial  ->
                       FStar_Pervasives_Native.Some ret_g
                   | FStar_TypeChecker_Common.NonTrivial vc2 ->
                       if Prims.op_Negation use_smt
                       then FStar_Pervasives_Native.None
                       else
                         ((let uu____15242 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15242
                           then
                             let uu____15243 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____15244 =
                               let uu____15245 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15245
                                in
                             FStar_Errors.diag uu____15243 uu____15244
                           else ());
                          (let vcs =
                             let uu____15251 = FStar_Options.use_tactics ()
                                in
                             if uu____15251
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)]  in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15265  ->
                                   match uu____15265 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          FStar_Pervasives_Native.Some ret_g))))
  
let discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15276 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____15276 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____15281 =
            let uu____15282 =
              let uu____15285 = FStar_TypeChecker_Env.get_range env  in
              ("Expected a trivial pre-condition", uu____15285)  in
            FStar_Errors.Error uu____15282  in
          raise uu____15281
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15292 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____15292 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15312 = FStar_Unionfind.find u  in
      match uu____15312 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15321 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____15336 = acc  in
      match uu____15336 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15382 = hd1  in
               (match uu____15382 with
                | (uu____15389,env,u,tm,k,r) ->
                    let uu____15395 = unresolved u  in
                    if uu____15395
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____15413 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____15413
                        then
                          let uu____15414 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____15418 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____15419 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15414 uu____15418 uu____15419
                        else ());
                       (let uu____15421 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15425 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15425.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15425.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15425.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15425.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15425.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15425.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15425.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15425.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15425.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15425.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15425.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15425.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15425.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15425.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15425.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15425.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15425.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15425.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15425.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15425.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15425.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15425.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15425.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____15421 with
                        | (uu____15426,uu____15427,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15430 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15430.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15430.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15430.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____15433 =
                                discharge_guard'
                                  (FStar_Pervasives_Native.Some
                                     (fun uu____15437  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____15433 with
                              | FStar_Pervasives_Native.Some g3 -> g3
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                               in
                            until_fixpoint
                              ((FStar_List.append
                                  g'.FStar_TypeChecker_Env.implicits out),
                                true) tl1))))
       in
    let uu___186_15452 = g  in
    let uu____15453 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15452.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15452.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15452.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15453
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15481 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____15481 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15488 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15488
      | (reason,uu____15490,uu____15491,e,t,r)::uu____15495 ->
          let uu____15509 =
            let uu____15510 = FStar_Syntax_Print.term_to_string t  in
            let uu____15511 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2
              "Failed to resolve implicit argument of type '%s' introduced in %s"
              uu____15510 uu____15511
             in
          FStar_Errors.err r uu____15509
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15518 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15518.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15518.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15518.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15536 = try_teq false env t1 t2  in
        match uu____15536 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g ->
            let uu____15539 =
              discharge_guard' FStar_Pervasives_Native.None env g false  in
            (match uu____15539 with
             | FStar_Pervasives_Native.Some uu____15543 -> true
             | FStar_Pervasives_Native.None  -> false)
  