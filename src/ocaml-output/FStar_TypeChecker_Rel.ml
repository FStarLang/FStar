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
                  Some uu____87  in
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
                (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
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
        FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
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
        let uu____215 =
          f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____215;
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
                       let uu____260 = FStar_Syntax_Syntax.is_null_binder b
                          in
                       if uu____260
                       then f1
                       else FStar_Syntax_Util.mk_forall u (fst b) f1) us bs f
               in
            let uu___136_262 = g  in
            {
              FStar_TypeChecker_Env.guard_f =
                (FStar_TypeChecker_Common.NonTrivial f1);
              FStar_TypeChecker_Env.deferred =
                (uu___136_262.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___136_262.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___136_262.FStar_TypeChecker_Env.implicits)
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
               let uu____276 = FStar_Syntax_Syntax.is_null_binder b  in
               if uu____276
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
            let uu___137_289 = g  in
            let uu____290 =
              let uu____291 = close_forall env binders f  in
              FStar_TypeChecker_Common.NonTrivial uu____291  in
            {
              FStar_TypeChecker_Env.guard_f = uu____290;
              FStar_TypeChecker_Env.deferred =
                (uu___137_289.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___137_289.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___137_289.FStar_TypeChecker_Env.implicits)
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
        let uv = FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar  in
        match binders with
        | [] ->
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uv1, uv1)
        | uu____332 ->
            let args =
              FStar_All.pipe_right binders
                (FStar_List.map FStar_Syntax_Util.arg_of_non_null_binder)
               in
            let k' =
              let uu____347 = FStar_Syntax_Syntax.mk_Total k  in
              FStar_Syntax_Util.arrow binders uu____347  in
            let uv1 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar (uv, k'))
                None r
               in
            let uu____363 =
              FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (uv1, args))
                (Some (k.FStar_Syntax_Syntax.n)) r
               in
            (uu____363, uv1)
  
let mk_eq2 :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____392 = FStar_Syntax_Util.type_u ()  in
        match uu____392 with
        | (t_type,u) ->
            let uu____397 =
              let uu____400 = FStar_TypeChecker_Env.all_binders env  in
              new_uvar t1.FStar_Syntax_Syntax.pos uu____400 t_type  in
            (match uu____397 with
             | (tt,uu____402) -> FStar_Syntax_Util.mk_eq2 u tt t1 t2)
  
type uvi =
  | TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
  FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let uu___is_TERM : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____425 -> false
  
let __proj__TERM__item___0 :
  uvi ->
    ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) *
      FStar_Syntax_Syntax.term)
  = fun projectee  -> match projectee with | TERM _0 -> _0 
let uu___is_UNIV : uvi -> Prims.bool =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____451 -> false
  
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
    match projectee with | Success _0 -> true | uu____539 -> false
  
let __proj__Success__item___0 : solution -> FStar_TypeChecker_Common.deferred
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : solution -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____553 -> false
  
let __proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * Prims.string) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let uu___is_COVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____570 -> false
  
let uu___is_CONTRAVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____574 -> false
  
let uu___is_INVARIANT : variance -> Prims.bool =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____578 -> false
  
type tprob =
  (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.term)
    FStar_TypeChecker_Common.problem
type cprob =
  (FStar_Syntax_Syntax.comp,Prims.unit) FStar_TypeChecker_Common.problem
type ('a,'b) problem_t = ('a,'b) FStar_TypeChecker_Common.problem
let rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string =
  fun uu___105_595  ->
    match uu___105_595 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let term_to_string env t =
  let uu____608 =
    let uu____609 = FStar_Syntax_Subst.compress t  in
    uu____609.FStar_Syntax_Syntax.n  in
  match uu____608 with
  | FStar_Syntax_Syntax.Tm_uvar (u,t1) ->
      let uu____626 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____630 = FStar_Syntax_Print.term_to_string t1  in
      FStar_Util.format2 "(%s:%s)" uu____626 uu____630
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (u,ty);
         FStar_Syntax_Syntax.tk = uu____633;
         FStar_Syntax_Syntax.pos = uu____634;
         FStar_Syntax_Syntax.vars = uu____635;_},args)
      ->
      let uu____663 = FStar_Syntax_Print.uvar_to_string u  in
      let uu____667 = FStar_Syntax_Print.term_to_string ty  in
      let uu____668 = FStar_Syntax_Print.args_to_string args  in
      FStar_Util.format3 "(%s:%s) %s" uu____663 uu____667 uu____668
  | uu____669 -> FStar_Syntax_Print.term_to_string t 
let prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string
  =
  fun env  ->
    fun uu___106_675  ->
      match uu___106_675 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____679 =
            let uu____681 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____682 =
              let uu____684 =
                term_to_string env p.FStar_TypeChecker_Common.lhs  in
              let uu____685 =
                let uu____687 =
                  FStar_Syntax_Print.tag_of_term
                    p.FStar_TypeChecker_Common.lhs
                   in
                let uu____688 =
                  let uu____690 =
                    let uu____692 =
                      term_to_string env p.FStar_TypeChecker_Common.rhs  in
                    let uu____693 =
                      let uu____695 =
                        FStar_Syntax_Print.tag_of_term
                          p.FStar_TypeChecker_Common.rhs
                         in
                      let uu____696 =
                        let uu____698 =
                          FStar_TypeChecker_Normalize.term_to_string env
                            (fst p.FStar_TypeChecker_Common.logical_guard)
                           in
                        let uu____699 =
                          let uu____701 =
                            FStar_All.pipe_right
                              p.FStar_TypeChecker_Common.reason
                              (FStar_String.concat "\n\t\t\t")
                             in
                          [uu____701]  in
                        uu____698 :: uu____699  in
                      uu____695 :: uu____696  in
                    uu____692 :: uu____693  in
                  (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                    uu____690
                   in
                uu____687 :: uu____688  in
              uu____684 :: uu____685  in
            uu____681 :: uu____682  in
          FStar_Util.format
            "\t%s: %s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>"
            uu____679
      | FStar_TypeChecker_Common.CProb p ->
          let uu____706 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____707 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" uu____706
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____707
  
let uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string =
  fun env  ->
    fun uu___107_713  ->
      match uu___107_713 with
      | UNIV (u,t) ->
          let x =
            let uu____717 = FStar_Options.hide_uvar_nums ()  in
            if uu____717
            then "?"
            else
              (let uu____719 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____719 FStar_Util.string_of_int)
             in
          let uu____721 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____721
      | TERM ((u,uu____723),t) ->
          let x =
            let uu____728 = FStar_Options.hide_uvar_nums ()  in
            if uu____728
            then "?"
            else
              (let uu____730 = FStar_Unionfind.uvar_id u  in
               FStar_All.pipe_right uu____730 FStar_Util.string_of_int)
             in
          let uu____734 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____734
  
let uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string =
  fun env  ->
    fun uvis  ->
      let uu____743 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____743 (FStar_String.concat ", ")
  
let names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string =
  fun nms  ->
    let uu____751 =
      let uu____753 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____753
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____751 (FStar_String.concat ", ")
  
let args_to_string args =
  let uu____771 =
    FStar_All.pipe_right args
      (FStar_List.map
         (fun uu____779  ->
            match uu____779 with
            | (x,uu____783) -> FStar_Syntax_Print.term_to_string x))
     in
  FStar_All.pipe_right uu____771 (FStar_String.concat " ") 
let empty_worklist : FStar_TypeChecker_Env.env -> worklist =
  fun env  ->
    let uu____788 =
      let uu____789 = FStar_Options.eager_inference ()  in
      Prims.op_Negation uu____789  in
    {
      attempting = [];
      wl_deferred = [];
      ctr = (Prims.parse_int "0");
      defer_ok = uu____788;
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
        let uu___138_802 = empty_worklist env  in
        {
          attempting = [prob];
          wl_deferred = (uu___138_802.wl_deferred);
          ctr = (uu___138_802.ctr);
          defer_ok = (uu___138_802.defer_ok);
          smt_ok;
          tcenv = (uu___138_802.tcenv)
        }
  
let singleton :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> worklist =
  fun env  -> fun prob  -> singleton' env prob true 
let wl_of_guard env g =
  let uu___139_827 = empty_worklist env  in
  let uu____828 = FStar_List.map FStar_Pervasives.snd g  in
  {
    attempting = uu____828;
    wl_deferred = (uu___139_827.wl_deferred);
    ctr = (uu___139_827.ctr);
    defer_ok = false;
    smt_ok = (uu___139_827.smt_ok);
    tcenv = (uu___139_827.tcenv)
  } 
let defer :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___140_840 = wl  in
        {
          attempting = (uu___140_840.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          ctr = (uu___140_840.ctr);
          defer_ok = (uu___140_840.defer_ok);
          smt_ok = (uu___140_840.smt_ok);
          tcenv = (uu___140_840.tcenv)
        }
  
let attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist =
  fun probs  ->
    fun wl  ->
      let uu___141_852 = wl  in
      {
        attempting = (FStar_List.append probs wl.attempting);
        wl_deferred = (uu___141_852.wl_deferred);
        ctr = (uu___141_852.ctr);
        defer_ok = (uu___141_852.defer_ok);
        smt_ok = (uu___141_852.smt_ok);
        tcenv = (uu___141_852.tcenv)
      }
  
let giveup :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____863 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____863
         then
           let uu____864 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" reason uu____864
         else ());
        Failed (prob, reason)
  
let invert_rel : FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel
  =
  fun uu___108_868  ->
    match uu___108_868 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert p =
  let uu___142_884 = p  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___142_884.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
    FStar_TypeChecker_Common.relation =
      (invert_rel p.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
    FStar_TypeChecker_Common.element =
      (uu___142_884.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___142_884.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___142_884.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___142_884.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___142_884.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___142_884.FStar_TypeChecker_Common.rank)
  } 
let maybe_invert p =
  if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
  then invert p
  else p 
let maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob =
  fun uu___109_905  ->
    match uu___109_905 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_32  -> FStar_TypeChecker_Common.TProb _0_32)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _0_33  -> FStar_TypeChecker_Common.CProb _0_33)
  
let vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel =
  fun rel  ->
    fun uu___110_921  ->
      match uu___110_921 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let p_pid : FStar_TypeChecker_Common.prob -> Prims.int =
  fun uu___111_924  ->
    match uu___111_924 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel =
  fun uu___112_933  ->
    match uu___112_933 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list =
  fun uu___113_943  ->
    match uu___113_943 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range =
  fun uu___114_953  ->
    match uu___114_953 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let p_guard :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
  =
  fun uu___115_964  ->
    match uu___115_964 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let p_scope : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.binders =
  fun uu___116_975  ->
    match uu___116_975 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.scope
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.scope
  
let p_invert : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun uu___117_984  ->
    match uu___117_984 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _0_34  -> FStar_TypeChecker_Common.TProb _0_34) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _0_35  -> FStar_TypeChecker_Common.CProb _0_35) (invert p)
  
let is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool =
  fun p  ->
    let uu____998 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____998 = (Prims.parse_int "1")
  
let next_pid : Prims.unit -> Prims.int =
  let ctr = FStar_Util.mk_ref (Prims.parse_int "0")  in
  fun uu____1009  -> FStar_Util.incr ctr; FStar_ST.read ctr 
let mk_problem scope orig lhs rel rhs elt reason =
  let uu____1059 = next_pid ()  in
  let uu____1060 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1059;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1060;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = (reason :: (p_reason orig));
    FStar_TypeChecker_Common.loc = (p_loc orig);
    FStar_TypeChecker_Common.rank = None
  } 
let new_problem env lhs rel rhs elt loc reason =
  let scope = FStar_TypeChecker_Env.all_binders env  in
  let uu____1107 = next_pid ()  in
  let uu____1108 =
    new_uvar FStar_Range.dummyRange scope FStar_Syntax_Util.ktype0  in
  {
    FStar_TypeChecker_Common.pid = uu____1107;
    FStar_TypeChecker_Common.lhs = lhs;
    FStar_TypeChecker_Common.relation = rel;
    FStar_TypeChecker_Common.rhs = rhs;
    FStar_TypeChecker_Common.element = elt;
    FStar_TypeChecker_Common.logical_guard = uu____1108;
    FStar_TypeChecker_Common.scope = scope;
    FStar_TypeChecker_Common.reason = [reason];
    FStar_TypeChecker_Common.loc = loc;
    FStar_TypeChecker_Common.rank = None
  } 
let problem_using_guard orig lhs rel rhs elt reason =
  let uu____1149 = next_pid ()  in
  {
    FStar_TypeChecker_Common.pid = uu____1149;
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
        let uu____1201 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ExplainRel")
           in
        if uu____1201
        then
          let uu____1202 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____1203 = prob_to_string env d  in
          let uu____1204 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____1202 uu____1203 uu____1204 s
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____1209 -> failwith "impossible"  in
           let uu____1210 =
             match d1 with
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____1218 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1219 =
                   FStar_TypeChecker_Normalize.term_to_string env
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1218, uu____1219)
             | FStar_TypeChecker_Common.CProb cp ->
                 let uu____1223 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.lhs
                    in
                 let uu____1224 =
                   FStar_TypeChecker_Normalize.comp_to_string env
                     cp.FStar_TypeChecker_Common.rhs
                    in
                 (uu____1223, uu____1224)
              in
           match uu____1210 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let commit : uvi Prims.list -> Prims.unit =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___118_1233  ->
            match uu___118_1233 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Unionfind.union u u'
                 | uu____1240 -> FStar_Unionfind.change u (Some t))
            | TERM ((u,uu____1243),t) -> FStar_Syntax_Util.set_uvar u t))
  
let find_term_uvar :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar -> uvi Prims.list -> FStar_Syntax_Syntax.term option
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___119_1266  ->
           match uu___119_1266 with
           | UNIV uu____1268 -> None
           | TERM ((u,uu____1272),t) ->
               let uu____1276 = FStar_Unionfind.equivalent uv u  in
               if uu____1276 then Some t else None)
  
let find_univ_uvar :
  FStar_Syntax_Syntax.universe option FStar_Unionfind.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.universe option
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___120_1295  ->
           match uu___120_1295 with
           | UNIV (u',t) ->
               let uu____1299 = FStar_Unionfind.equivalent u u'  in
               if uu____1299 then Some t else None
           | uu____1303 -> None)
  
let whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1310 =
        let uu____1311 = FStar_Syntax_Util.unmeta t  in
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF] env uu____1311
         in
      FStar_Syntax_Subst.compress uu____1310
  
let sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let uu____1318 =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta] env t
         in
      FStar_Syntax_Subst.compress uu____1318
  
let norm_arg env t =
  let uu____1337 = sn env (fst t)  in (uu____1337, (snd t)) 
let sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____1354  ->
              match uu____1354 with
              | (x,imp) ->
                  let uu____1361 =
                    let uu___143_1362 = x  in
                    let uu____1363 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___143_1362.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___143_1362.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1363
                    }  in
                  (uu____1361, imp)))
  
let norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____1378 = aux u3  in FStar_Syntax_Syntax.U_succ uu____1378
        | FStar_Syntax_Syntax.U_max us ->
            let uu____1381 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____1381
        | uu____1383 -> u2  in
      let uu____1384 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____1384
  
let normalize_refinement steps env wl t0 =
  FStar_TypeChecker_Normalize.normalize_refinement steps env t0 
let base_and_refinement env wl t1 =
  let rec aux norm t11 =
    match t11.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
        if norm
        then ((x.FStar_Syntax_Syntax.sort), (Some (x, phi)))
        else
          (let uu____1491 =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           match uu____1491 with
           | {
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1);
               FStar_Syntax_Syntax.tk = uu____1503;
               FStar_Syntax_Syntax.pos = uu____1504;
               FStar_Syntax_Syntax.vars = uu____1505;_} ->
               ((x1.FStar_Syntax_Syntax.sort), (Some (x1, phi1)))
           | tt ->
               let uu____1526 =
                 let uu____1527 = FStar_Syntax_Print.term_to_string tt  in
                 let uu____1528 = FStar_Syntax_Print.tag_of_term tt  in
                 FStar_Util.format2 "impossible: Got %s ... %s\n" uu____1527
                   uu____1528
                  in
               failwith uu____1526)
    | FStar_Syntax_Syntax.Tm_uinst uu____1538 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1565 =
             let uu____1566 = FStar_Syntax_Subst.compress t1'  in
             uu____1566.FStar_Syntax_Syntax.n  in
           match uu____1565 with
           | FStar_Syntax_Syntax.Tm_refine uu____1578 -> aux true t1'
           | uu____1583 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_fvar uu____1595 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1618 =
             let uu____1619 = FStar_Syntax_Subst.compress t1'  in
             uu____1619.FStar_Syntax_Syntax.n  in
           match uu____1618 with
           | FStar_Syntax_Syntax.Tm_refine uu____1631 -> aux true t1'
           | uu____1636 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_app uu____1648 ->
        if norm
        then (t11, None)
        else
          (let t1' =
             normalize_refinement [FStar_TypeChecker_Normalize.WHNF] env wl
               t11
              in
           let uu____1680 =
             let uu____1681 = FStar_Syntax_Subst.compress t1'  in
             uu____1681.FStar_Syntax_Syntax.n  in
           match uu____1680 with
           | FStar_Syntax_Syntax.Tm_refine uu____1693 -> aux true t1'
           | uu____1698 -> (t11, None))
    | FStar_Syntax_Syntax.Tm_type uu____1710 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_constant uu____1722 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_name uu____1734 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_bvar uu____1746 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_arrow uu____1758 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_abs uu____1777 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_uvar uu____1803 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_let uu____1823 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_match uu____1842 -> (t11, None)
    | FStar_Syntax_Syntax.Tm_meta uu____1869 ->
        let uu____1874 =
          let uu____1875 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1876 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1875
            uu____1876
           in
        failwith uu____1874
    | FStar_Syntax_Syntax.Tm_ascribed uu____1886 ->
        let uu____1904 =
          let uu____1905 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1906 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1905
            uu____1906
           in
        failwith uu____1904
    | FStar_Syntax_Syntax.Tm_delayed uu____1916 ->
        let uu____1937 =
          let uu____1938 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1939 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1938
            uu____1939
           in
        failwith uu____1937
    | FStar_Syntax_Syntax.Tm_unknown  ->
        let uu____1949 =
          let uu____1950 = FStar_Syntax_Print.term_to_string t11  in
          let uu____1951 = FStar_Syntax_Print.tag_of_term t11  in
          FStar_Util.format2 "impossible (outer): Got %s ... %s\n" uu____1950
            uu____1951
           in
        failwith uu____1949
     in
  let uu____1961 = whnf env t1  in aux false uu____1961 
let unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun env  ->
    fun t  ->
      let uu____1970 =
        let uu____1980 = empty_worklist env  in
        base_and_refinement env uu____1980 t  in
      FStar_All.pipe_right uu____1970 FStar_Pervasives.fst
  
let trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
  =
  fun t  ->
    let uu____2004 = FStar_Syntax_Syntax.null_bv t  in
    (uu____2004, FStar_Syntax_Util.t_true)
  
let as_refinement env wl t =
  let uu____2024 = base_and_refinement env wl t  in
  match uu____2024 with
  | (t_base,refinement) ->
      (match refinement with
       | None  -> trivial_refinement t_base
       | Some (x,phi) -> (x, phi))
  
let force_refinement uu____2083 =
  match uu____2083 with
  | (t_base,refopt) ->
      let uu____2097 =
        match refopt with
        | Some (y,phi) -> (y, phi)
        | None  -> trivial_refinement t_base  in
      (match uu____2097 with
       | (y,phi) ->
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
             None t_base.FStar_Syntax_Syntax.pos)
  
let wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string =
  fun wl  ->
    fun uu___121_2121  ->
      match uu___121_2121 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2125 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2126 =
            let uu____2127 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
            FStar_Syntax_Print.term_to_string uu____2127  in
          let uu____2128 =
            let uu____2129 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
            FStar_Syntax_Print.term_to_string uu____2129  in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2125 uu____2126
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2128
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2133 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____2134 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____2135 =
            FStar_TypeChecker_Normalize.comp_to_string wl.tcenv
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "%s: %s  (%s)  %s" uu____2133 uu____2134
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____2135
  
let wl_to_string : worklist -> Prims.string =
  fun wl  ->
    let uu____2139 =
      let uu____2141 =
        let uu____2143 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____2153  ->
                  match uu____2153 with | (uu____2157,uu____2158,x) -> x))
           in
        FStar_List.append wl.attempting uu____2143  in
      FStar_List.map (wl_prob_to_string wl) uu____2141  in
    FStar_All.pipe_right uu____2139 (FStar_String.concat "\n\t")
  
let u_abs :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____2176 =
          let uu____2186 =
            let uu____2187 = FStar_Syntax_Subst.compress k  in
            uu____2187.FStar_Syntax_Syntax.n  in
          match uu____2186 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____2228 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____2228)
              else
                (let uu____2242 = FStar_Syntax_Util.abs_formals t  in
                 match uu____2242 with
                 | (ys',t1,uu____2263) ->
                     let uu____2276 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____2276))
          | uu____2297 ->
              let uu____2298 =
                let uu____2304 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____2304)  in
              ((ys, t), uu____2298)
           in
        match uu____2176 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (Some
                   (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid, [])))
            else
              (let c1 =
                 let uu____2359 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____2359 c  in
               let uu____2361 =
                 let uu____2368 =
                   FStar_All.pipe_right (FStar_Syntax_Util.lcomp_of_comp c1)
                     (fun _0_36  -> FStar_Util.Inl _0_36)
                    in
                 FStar_All.pipe_right uu____2368 (fun _0_37  -> Some _0_37)
                  in
               FStar_Syntax_Util.abs ys1 t1 uu____2361)
  
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
            let uu____2419 = p_guard prob  in
            match uu____2419 with
            | (uu____2422,uv) ->
                ((let uu____2425 =
                    let uu____2426 = FStar_Syntax_Subst.compress uv  in
                    uu____2426.FStar_Syntax_Syntax.n  in
                  match uu____2425 with
                  | FStar_Syntax_Syntax.Tm_uvar (uvar,k) ->
                      let bs = p_scope prob  in
                      let phi1 = u_abs k bs phi  in
                      ((let uu____2446 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug wl.tcenv)
                            (FStar_Options.Other "Rel")
                           in
                        if uu____2446
                        then
                          let uu____2447 =
                            FStar_Util.string_of_int (p_pid prob)  in
                          let uu____2448 =
                            FStar_Syntax_Print.term_to_string uv  in
                          let uu____2449 =
                            FStar_Syntax_Print.term_to_string phi1  in
                          FStar_Util.print3
                            "Solving %s (%s) with formula %s\n" uu____2447
                            uu____2448 uu____2449
                        else ());
                       FStar_Syntax_Util.set_uvar uvar phi1)
                  | uu____2453 ->
                      if Prims.op_Negation resolve_ok
                      then
                        failwith
                          "Impossible: this instance has already been assigned a solution"
                      else ());
                 commit uvis;
                 (let uu___144_2456 = wl  in
                  {
                    attempting = (uu___144_2456.attempting);
                    wl_deferred = (uu___144_2456.wl_deferred);
                    ctr = (wl.ctr + (Prims.parse_int "1"));
                    defer_ok = (uu___144_2456.defer_ok);
                    smt_ok = (uu___144_2456.smt_ok);
                    tcenv = (uu___144_2456.tcenv)
                  }))
  
let extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____2469 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "RelCheck")
            in
         if uu____2469
         then
           let uu____2470 = FStar_Util.string_of_int pid  in
           let uu____2471 =
             let uu____2472 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____2472 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with %s\n" uu____2470 uu____2471
         else ());
        commit sol;
        (let uu___145_2477 = wl  in
         {
           attempting = (uu___145_2477.attempting);
           wl_deferred = (uu___145_2477.wl_deferred);
           ctr = (wl.ctr + (Prims.parse_int "1"));
           defer_ok = (uu___145_2477.defer_ok);
           smt_ok = (uu___145_2477.smt_ok);
           tcenv = (uu___145_2477.tcenv)
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
            | (uu____2506,FStar_TypeChecker_Common.Trivial ) -> t
            | (None ,FStar_TypeChecker_Common.NonTrivial f) -> Some f
            | (Some t1,FStar_TypeChecker_Common.NonTrivial f) ->
                let uu____2514 = FStar_Syntax_Util.mk_conj t1 f  in
                Some uu____2514
             in
          (let uu____2520 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "RelCheck")
              in
           if uu____2520
           then
             let uu____2521 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____2522 =
               let uu____2523 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____2523 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____2521 uu____2522
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let rec occurs wl uk t =
  let uu____2548 =
    let uu____2552 = FStar_Syntax_Free.uvars t  in
    FStar_All.pipe_right uu____2552 FStar_Util.set_elements  in
  FStar_All.pipe_right uu____2548
    (FStar_Util.for_some
       (fun uu____2573  ->
          match uu____2573 with
          | (uv,uu____2581) -> FStar_Unionfind.equivalent uv (fst uk)))
  
let occurs_check env wl uk t =
  let occurs_ok =
    let uu____2625 = occurs wl uk t  in Prims.op_Negation uu____2625  in
  let msg =
    if occurs_ok
    then None
    else
      (let uu____2630 =
         let uu____2631 = FStar_Syntax_Print.uvar_to_string (fst uk)  in
         let uu____2635 = FStar_Syntax_Print.term_to_string t  in
         FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
           uu____2631 uu____2635
          in
       Some uu____2630)
     in
  (occurs_ok, msg) 
let occurs_and_freevars_check env wl uk fvs t =
  let fvs_t = FStar_Syntax_Free.names t  in
  let uu____2683 = occurs_check env wl uk t  in
  match uu____2683 with
  | (occurs_ok,msg) ->
      let uu____2700 = FStar_Util.set_is_subset_of fvs_t fvs  in
      (occurs_ok, uu____2700, (msg, fvs, fvs_t))
  
let intersect_vars v1 v2 =
  let as_set1 v3 =
    FStar_All.pipe_right v3
      (FStar_List.fold_left
         (fun out  -> fun x  -> FStar_Util.set_add (fst x) out)
         FStar_Syntax_Syntax.no_names)
     in
  let v1_set = as_set1 v1  in
  let uu____2764 =
    FStar_All.pipe_right v2
      (FStar_List.fold_left
         (fun uu____2788  ->
            fun uu____2789  ->
              match (uu____2788, uu____2789) with
              | ((isect,isect_set),(x,imp)) ->
                  let uu____2832 =
                    let uu____2833 = FStar_Util.set_mem x v1_set  in
                    FStar_All.pipe_left Prims.op_Negation uu____2833  in
                  if uu____2832
                  then (isect, isect_set)
                  else
                    (let fvs =
                       FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort  in
                     let uu____2847 =
                       FStar_Util.set_is_subset_of fvs isect_set  in
                     if uu____2847
                     then
                       let uu____2854 = FStar_Util.set_add x isect_set  in
                       (((x, imp) :: isect), uu____2854)
                     else (isect, isect_set)))
         ([], FStar_Syntax_Syntax.no_names))
     in
  match uu____2764 with | (isect,uu____2876) -> FStar_List.rev isect 
let binders_eq v1 v2 =
  ((FStar_List.length v1) = (FStar_List.length v2)) &&
    (FStar_List.forall2
       (fun uu____2925  ->
          fun uu____2926  ->
            match (uu____2925, uu____2926) with
            | ((a,uu____2936),(b,uu____2938)) ->
                FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let pat_var_opt env seen arg =
  let hd1 = norm_arg env arg  in
  match (fst hd1).FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_name a ->
      let uu____2982 =
        FStar_All.pipe_right seen
          (FStar_Util.for_some
             (fun uu____2988  ->
                match uu____2988 with
                | (b,uu____2992) -> FStar_Syntax_Syntax.bv_eq a b))
         in
      if uu____2982 then None else Some (a, (snd hd1))
  | uu____3001 -> None 
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
            let uu____3044 = pat_var_opt env seen hd1  in
            (match uu____3044 with
             | None  ->
                 ((let uu____3052 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Rel")
                      in
                   if uu____3052
                   then
                     let uu____3053 =
                       FStar_All.pipe_left FStar_Syntax_Print.term_to_string
                         (fst hd1)
                        in
                     FStar_Util.print1 "Not a pattern: %s\n" uu____3053
                   else ());
                  None)
             | Some x -> pat_vars env (x :: seen) rest)
  
let is_flex : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3065 =
      let uu____3066 = FStar_Syntax_Subst.compress t  in
      uu____3066.FStar_Syntax_Syntax.n  in
    match uu____3065 with
    | FStar_Syntax_Syntax.Tm_uvar uu____3069 -> true
    | FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar uu____3078;
           FStar_Syntax_Syntax.tk = uu____3079;
           FStar_Syntax_Syntax.pos = uu____3080;
           FStar_Syntax_Syntax.vars = uu____3081;_},uu____3082)
        -> true
    | uu____3105 -> false
  
let destruct_flex_t t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_uvar (uv,k) -> (t, uv, k, [])
  | FStar_Syntax_Syntax.Tm_app
      ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv,k);
         FStar_Syntax_Syntax.tk = uu____3167;
         FStar_Syntax_Syntax.pos = uu____3168;
         FStar_Syntax_Syntax.vars = uu____3169;_},args)
      -> (t, uv, k, args)
  | uu____3210 -> failwith "Not a flex-uvar" 
let destruct_flex_pattern env t =
  let uu____3264 = destruct_flex_t t  in
  match uu____3264 with
  | (t1,uv,k,args) ->
      let uu____3332 = pat_vars env [] args  in
      (match uu____3332 with
       | Some vars -> ((t1, uv, k, args), (Some vars))
       | uu____3388 -> ((t1, uv, k, args), None))
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth option *
  FStar_Syntax_Syntax.delta_depth option) 
  | HeadMatch 
  | FullMatch 
let uu___is_MisMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____3437 -> false
  
let __proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth option * FStar_Syntax_Syntax.delta_depth
      option)
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let uu___is_HeadMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | HeadMatch  -> true | uu____3460 -> false
  
let uu___is_FullMatch : match_result -> Prims.bool =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____3464 -> false
  
let head_match : match_result -> match_result =
  fun uu___122_3467  ->
    match uu___122_3467 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | uu____3476 -> HeadMatch
  
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
      | FStar_Syntax_Syntax.Delta_defined_at_level uu____3489 ->
          let uu____3490 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.Delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____3490 with
           | None  -> FStar_Syntax_Syntax.Delta_constant
           | uu____3500 -> fv.FStar_Syntax_Syntax.fv_delta)
      | d -> d
  
let rec delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth option
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____3514 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____3520 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> None
      | FStar_Syntax_Syntax.Tm_bvar uu____3542 -> None
      | FStar_Syntax_Syntax.Tm_name uu____3543 -> None
      | FStar_Syntax_Syntax.Tm_uvar uu____3544 -> None
      | FStar_Syntax_Syntax.Tm_let uu____3553 -> None
      | FStar_Syntax_Syntax.Tm_match uu____3561 -> None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____3578) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____3584,uu____3585) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____3615) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____3630;
             FStar_Syntax_Syntax.index = uu____3631;
             FStar_Syntax_Syntax.sort = t2;_},uu____3633)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____3640 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____3641 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____3642 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____3650 ->
          Some FStar_Syntax_Syntax.Delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3666 = fv_delta_depth env fv  in Some uu____3666
  
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
            let uu____3685 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____3685
            then FullMatch
            else
              (let uu____3687 =
                 let uu____3692 =
                   let uu____3694 = fv_delta_depth env f  in Some uu____3694
                    in
                 let uu____3695 =
                   let uu____3697 = fv_delta_depth env g  in Some uu____3697
                    in
                 (uu____3692, uu____3695)  in
               MisMatch uu____3687)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____3701),FStar_Syntax_Syntax.Tm_uinst (g,uu____3703)) ->
            let uu____3712 = head_matches env f g  in
            FStar_All.pipe_right uu____3712 head_match
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) -> if c = d then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____3719),FStar_Syntax_Syntax.Tm_uvar (uv',uu____3721)) ->
            let uu____3746 = FStar_Unionfind.equivalent uv uv'  in
            if uu____3746 then FullMatch else MisMatch (None, None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____3754),FStar_Syntax_Syntax.Tm_refine (y,uu____3756)) ->
            let uu____3765 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3765 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____3767),uu____3768) ->
            let uu____3773 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____3773 head_match
        | (uu____3774,FStar_Syntax_Syntax.Tm_refine (x,uu____3776)) ->
            let uu____3781 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____3781 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____3782,FStar_Syntax_Syntax.Tm_type
           uu____3783) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____3784,FStar_Syntax_Syntax.Tm_arrow uu____3785) -> HeadMatch
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____3801),FStar_Syntax_Syntax.Tm_app (head',uu____3803))
            ->
            let uu____3832 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____3832 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____3834),uu____3835) ->
            let uu____3850 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____3850 head_match
        | (uu____3851,FStar_Syntax_Syntax.Tm_app (head1,uu____3853)) ->
            let uu____3868 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____3868 head_match
        | uu____3869 ->
            let uu____3872 =
              let uu____3877 = delta_depth_of_term env t11  in
              let uu____3879 = delta_depth_of_term env t21  in
              (uu____3877, uu____3879)  in
            MisMatch uu____3872
  
let head_matches_delta env wl t1 t2 =
  let maybe_inline t =
    let uu____3915 = FStar_Syntax_Util.head_and_args t  in
    match uu____3915 with
    | (head1,uu____3927) ->
        let uu____3942 =
          let uu____3943 = FStar_Syntax_Util.un_uinst head1  in
          uu____3943.FStar_Syntax_Syntax.n  in
        (match uu____3942 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let uu____3948 =
               let uu____3949 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Eager_unfolding_only] env
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               FStar_All.pipe_right uu____3949 FStar_Option.isSome  in
             if uu____3948
             then
               let uu____3963 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Normalize.Beta;
                   FStar_TypeChecker_Normalize.Eager_unfolding] env t
                  in
               FStar_All.pipe_right uu____3963 (fun _0_38  -> Some _0_38)
             else None
         | uu____3966 -> None)
     in
  let success d r t11 t21 =
    (r, (if d > (Prims.parse_int "0") then Some (t11, t21) else None))  in
  let fail r = (r, None)  in
  let rec aux retry n_delta t11 t21 =
    let r = head_matches env t11 t21  in
    match r with
    | MisMatch (Some (FStar_Syntax_Syntax.Delta_equational ),uu____4034) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4044 =
             let uu____4049 = maybe_inline t11  in
             let uu____4051 = maybe_inline t21  in (uu____4049, uu____4051)
              in
           match uu____4044 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (uu____4072,Some (FStar_Syntax_Syntax.Delta_equational )) ->
        if Prims.op_Negation retry
        then fail r
        else
          (let uu____4082 =
             let uu____4087 = maybe_inline t11  in
             let uu____4089 = maybe_inline t21  in (uu____4087, uu____4089)
              in
           match uu____4082 with
           | (None ,None ) -> fail r
           | (Some t12,None ) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t21
           | (None ,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t11 t22
           | (Some t12,Some t22) ->
               aux false (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch (Some d1,Some d2) when d1 = d2 ->
        let uu____4114 = FStar_TypeChecker_Common.decr_delta_depth d1  in
        (match uu____4114 with
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
        let uu____4129 =
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
             let uu____4137 =
               normalize_refinement
                 [FStar_TypeChecker_Normalize.UnfoldUntil d1;
                 FStar_TypeChecker_Normalize.WHNF] env wl t21
                in
             (t11, uu____4137))
           in
        (match uu____4129 with
         | (t12,t22) -> aux retry (n_delta + (Prims.parse_int "1")) t12 t22)
    | MisMatch uu____4145 -> fail r
    | uu____4150 -> success n_delta r t11 t21  in
  aux true (Prims.parse_int "0") t1 t2 
type tc =
  | T of (FStar_Syntax_Syntax.term *
  (FStar_Syntax_Syntax.binders ->
     FStar_Range.range -> FStar_Syntax_Syntax.term))
  
  | C of FStar_Syntax_Syntax.comp 
let uu___is_T : tc -> Prims.bool =
  fun projectee  -> match projectee with | T _0 -> true | uu____4179 -> false 
let __proj__T__item___0 :
  tc ->
    (FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.binders ->
         FStar_Range.range -> FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | T _0 -> _0 
let uu___is_C : tc -> Prims.bool =
  fun projectee  -> match projectee with | C _0 -> true | uu____4209 -> false 
let __proj__C__item___0 : tc -> FStar_Syntax_Syntax.comp =
  fun projectee  -> match projectee with | C _0 -> _0 
type tcs = tc Prims.list
let generic_kind :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4224 = FStar_Syntax_Util.type_u ()  in
      match uu____4224 with
      | (t,uu____4228) ->
          let uu____4229 = new_uvar r binders t  in fst uu____4229
  
let kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ
  =
  fun binders  ->
    fun r  ->
      let uu____4238 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____4238 FStar_Pervasives.fst
  
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
        let uu____4280 = head_matches env t1 t'  in
        match uu____4280 with
        | MisMatch uu____4281 -> false
        | uu____4286 -> true  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rebuild args' =
            let args1 =
              FStar_List.map2
                (fun x  ->
                   fun y  ->
                     match (x, y) with
                     | ((uu____4346,imp),T (t2,uu____4349)) -> (t2, imp)
                     | uu____4366 -> failwith "Bad reconstruction") args
                args'
               in
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (hd1, args1))
              None t1.FStar_Syntax_Syntax.pos
             in
          let tcs =
            FStar_All.pipe_right args
              (FStar_List.map
                 (fun uu____4406  ->
                    match uu____4406 with
                    | (t2,uu____4414) ->
                        (None, INVARIANT, (T (t2, generic_kind)))))
             in
          (rebuild, matches, tcs)
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let fail uu____4447 = failwith "Bad reconstruction"  in
          let uu____4448 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____4448 with
           | (bs1,c1) ->
               let rebuild tcs =
                 let rec aux out bs2 tcs1 =
                   match (bs2, tcs1) with
                   | ((x,imp)::bs3,(T (t2,uu____4501))::tcs2) ->
                       aux
                         (((let uu___146_4523 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___146_4523.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___146_4523.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t2
                            }), imp) :: out) bs3 tcs2
                   | ([],(C c2)::[]) ->
                       FStar_Syntax_Util.arrow (FStar_List.rev out) c2
                   | uu____4533 -> failwith "Bad reconstruction"  in
                 aux [] bs1 tcs  in
               let rec decompose1 out uu___123_4564 =
                 match uu___123_4564 with
                 | [] -> FStar_List.rev ((None, COVARIANT, (C c1)) :: out)
                 | hd1::rest ->
                     decompose1
                       (((Some hd1), CONTRAVARIANT,
                          (T
                             (((fst hd1).FStar_Syntax_Syntax.sort),
                               kind_type))) :: out) rest
                  in
               let uu____4627 = decompose1 [] bs1  in
               (rebuild, matches, uu____4627))
      | uu____4655 ->
          let rebuild uu___124_4660 =
            match uu___124_4660 with
            | [] -> t1
            | uu____4662 -> failwith "Bad reconstruction"  in
          (rebuild, ((fun t2  -> true)), [])
  
let un_T : tc -> FStar_Syntax_Syntax.term =
  fun uu___125_4681  ->
    match uu___125_4681 with
    | T (t,uu____4683) -> t
    | uu____4692 -> failwith "Impossible"
  
let arg_of_tc : tc -> FStar_Syntax_Syntax.arg =
  fun uu___126_4695  ->
    match uu___126_4695 with
    | T (t,uu____4697) -> FStar_Syntax_Syntax.as_arg t
    | uu____4706 -> failwith "Impossible"
  
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
              | (uu____4775,variance,T (ti,mk_kind)) ->
                  let k = mk_kind scope1 r  in
                  let uu____4794 = new_uvar r scope1 k  in
                  (match uu____4794 with
                   | (gi_xs,gi) ->
                       let gi_ps =
                         match args with
                         | [] -> gi
                         | uu____4806 ->
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_app (gi, args)) None r
                          in
                       let uu____4821 =
                         let uu____4822 =
                           mk_problem scope1 orig gi_ps
                             (vary_rel rel variance) ti None "type subterm"
                            in
                         FStar_All.pipe_left
                           (fun _0_39  ->
                              FStar_TypeChecker_Common.TProb _0_39)
                           uu____4822
                          in
                       ((T (gi_xs, mk_kind)), uu____4821))
              | (uu____4831,uu____4832,C uu____4833) -> failwith "impos"  in
            let rec aux scope1 args qs1 =
              match qs1 with
              | [] -> ([], [], FStar_Syntax_Util.t_true)
              | q::qs2 ->
                  let uu____4920 =
                    match q with
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4931;
                         FStar_Syntax_Syntax.pos = uu____4932;
                         FStar_Syntax_Syntax.vars = uu____4933;_})
                        ->
                        let uu____4948 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____4948 with
                         | (T (gi_xs,uu____4964),prob) ->
                             let uu____4974 =
                               let uu____4975 =
                                 FStar_Syntax_Syntax.mk_Total' gi_xs uopt  in
                               FStar_All.pipe_left (fun _0_40  -> C _0_40)
                                 uu____4975
                                in
                             (uu____4974, [prob])
                         | uu____4977 -> failwith "impossible")
                    | (bopt,variance,C
                       {
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal
                           (ti,uopt);
                         FStar_Syntax_Syntax.tk = uu____4987;
                         FStar_Syntax_Syntax.pos = uu____4988;
                         FStar_Syntax_Syntax.vars = uu____4989;_})
                        ->
                        let uu____5004 =
                          sub_prob scope1 args
                            (bopt, variance, (T (ti, kind_type)))
                           in
                        (match uu____5004 with
                         | (T (gi_xs,uu____5020),prob) ->
                             let uu____5030 =
                               let uu____5031 =
                                 FStar_Syntax_Syntax.mk_GTotal' gi_xs uopt
                                  in
                               FStar_All.pipe_left (fun _0_41  -> C _0_41)
                                 uu____5031
                                in
                             (uu____5030, [prob])
                         | uu____5033 -> failwith "impossible")
                    | (uu____5039,uu____5040,C
                       { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp c;
                         FStar_Syntax_Syntax.tk = uu____5042;
                         FStar_Syntax_Syntax.pos = uu____5043;
                         FStar_Syntax_Syntax.vars = uu____5044;_})
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
                        let uu____5118 =
                          let uu____5123 =
                            FStar_List.map (sub_prob scope1 args) components1
                             in
                          FStar_All.pipe_right uu____5123 FStar_List.unzip
                           in
                        (match uu____5118 with
                         | (tcs,sub_probs) ->
                             let gi_xs =
                               let uu____5152 =
                                 let uu____5153 =
                                   let uu____5156 = FStar_List.hd tcs  in
                                   FStar_All.pipe_right uu____5156 un_T  in
                                 let uu____5157 =
                                   let uu____5163 = FStar_List.tl tcs  in
                                   FStar_All.pipe_right uu____5163
                                     (FStar_List.map arg_of_tc)
                                    in
                                 {
                                   FStar_Syntax_Syntax.comp_univs =
                                     (c.FStar_Syntax_Syntax.comp_univs);
                                   FStar_Syntax_Syntax.effect_name =
                                     (c.FStar_Syntax_Syntax.effect_name);
                                   FStar_Syntax_Syntax.result_typ =
                                     uu____5153;
                                   FStar_Syntax_Syntax.effect_args =
                                     uu____5157;
                                   FStar_Syntax_Syntax.flags =
                                     (c.FStar_Syntax_Syntax.flags)
                                 }  in
                               FStar_All.pipe_left
                                 FStar_Syntax_Syntax.mk_Comp uu____5152
                                in
                             ((C gi_xs), sub_probs))
                    | uu____5168 ->
                        let uu____5175 = sub_prob scope1 args q  in
                        (match uu____5175 with
                         | (ktec,prob) -> (ktec, [prob]))
                     in
                  (match uu____4920 with
                   | (tc,probs) ->
                       let uu____5193 =
                         match q with
                         | (Some b,uu____5219,uu____5220) ->
                             let uu____5228 =
                               let uu____5232 =
                                 FStar_Syntax_Util.arg_of_non_null_binder b
                                  in
                               uu____5232 :: args  in
                             ((Some b), (b :: scope1), uu____5228)
                         | uu____5250 -> (None, scope1, args)  in
                       (match uu____5193 with
                        | (bopt,scope2,args1) ->
                            let uu____5293 = aux scope2 args1 qs2  in
                            (match uu____5293 with
                             | (sub_probs,tcs,f) ->
                                 let f1 =
                                   match bopt with
                                   | None  ->
                                       let uu____5314 =
                                         let uu____5316 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         f :: uu____5316  in
                                       FStar_Syntax_Util.mk_conj_l uu____5314
                                   | Some b ->
                                       let u_b =
                                         env.FStar_TypeChecker_Env.universe_of
                                           env
                                           (fst b).FStar_Syntax_Syntax.sort
                                          in
                                       let uu____5329 =
                                         let uu____5331 =
                                           FStar_Syntax_Util.mk_forall u_b
                                             (fst b) f
                                            in
                                         let uu____5332 =
                                           FStar_All.pipe_right probs
                                             (FStar_List.map
                                                (fun prob  ->
                                                   FStar_All.pipe_right
                                                     (p_guard prob)
                                                     FStar_Pervasives.fst))
                                            in
                                         uu____5331 :: uu____5332  in
                                       FStar_Syntax_Util.mk_conj_l uu____5329
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
  let uu___147_5385 = p  in
  let uu____5388 = whnf wl.tcenv p.FStar_TypeChecker_Common.lhs  in
  let uu____5389 = whnf wl.tcenv p.FStar_TypeChecker_Common.rhs  in
  {
    FStar_TypeChecker_Common.pid =
      (uu___147_5385.FStar_TypeChecker_Common.pid);
    FStar_TypeChecker_Common.lhs = uu____5388;
    FStar_TypeChecker_Common.relation =
      (uu___147_5385.FStar_TypeChecker_Common.relation);
    FStar_TypeChecker_Common.rhs = uu____5389;
    FStar_TypeChecker_Common.element =
      (uu___147_5385.FStar_TypeChecker_Common.element);
    FStar_TypeChecker_Common.logical_guard =
      (uu___147_5385.FStar_TypeChecker_Common.logical_guard);
    FStar_TypeChecker_Common.scope =
      (uu___147_5385.FStar_TypeChecker_Common.scope);
    FStar_TypeChecker_Common.reason =
      (uu___147_5385.FStar_TypeChecker_Common.reason);
    FStar_TypeChecker_Common.loc =
      (uu___147_5385.FStar_TypeChecker_Common.loc);
    FStar_TypeChecker_Common.rank =
      (uu___147_5385.FStar_TypeChecker_Common.rank)
  } 
let compress_prob :
  worklist -> FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob
  =
  fun wl  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____5399 = compress_tprob wl p1  in
          FStar_All.pipe_right uu____5399
            (fun _0_42  -> FStar_TypeChecker_Common.TProb _0_42)
      | FStar_TypeChecker_Common.CProb uu____5404 -> p
  
let rank :
  worklist ->
    FStar_TypeChecker_Common.prob ->
      (Prims.int * FStar_TypeChecker_Common.prob)
  =
  fun wl  ->
    fun pr  ->
      let prob =
        let uu____5418 = compress_prob wl pr  in
        FStar_All.pipe_right uu____5418 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____5424 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____5424 with
           | (lh,uu____5437) ->
               let uu____5452 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____5452 with
                | (rh,uu____5465) ->
                    let uu____5480 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____5489,FStar_Syntax_Syntax.Tm_uvar uu____5490)
                          -> (flex_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5509,uu____5510)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (uu____5521,FStar_Syntax_Syntax.Tm_uvar uu____5522)
                          when
                          (tp.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ)
                            || (FStar_Options.eager_inference ())
                          -> (flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____5533,uu____5534)
                          ->
                          let uu____5543 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.rhs
                             in
                          (match uu____5543 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (flex_rigid, tp)
                                | uu____5583 ->
                                    let rank =
                                      let uu____5590 = is_top_level_prob prob
                                         in
                                      if uu____5590
                                      then flex_refine
                                      else flex_refine_inner  in
                                    let uu____5592 =
                                      let uu___148_5595 = tp  in
                                      let uu____5598 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___148_5595.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          (uu___148_5595.FStar_TypeChecker_Common.lhs);
                                        FStar_TypeChecker_Common.relation =
                                          (uu___148_5595.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          uu____5598;
                                        FStar_TypeChecker_Common.element =
                                          (uu___148_5595.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___148_5595.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___148_5595.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___148_5595.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___148_5595.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___148_5595.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (rank, uu____5592)))
                      | (uu____5608,FStar_Syntax_Syntax.Tm_uvar uu____5609)
                          ->
                          let uu____5618 =
                            base_and_refinement wl.tcenv wl
                              tp.FStar_TypeChecker_Common.lhs
                             in
                          (match uu____5618 with
                           | (b,ref_opt) ->
                               (match ref_opt with
                                | None  -> (rigid_flex, tp)
                                | uu____5658 ->
                                    let uu____5664 =
                                      let uu___149_5669 = tp  in
                                      let uu____5672 =
                                        force_refinement (b, ref_opt)  in
                                      {
                                        FStar_TypeChecker_Common.pid =
                                          (uu___149_5669.FStar_TypeChecker_Common.pid);
                                        FStar_TypeChecker_Common.lhs =
                                          uu____5672;
                                        FStar_TypeChecker_Common.relation =
                                          (uu___149_5669.FStar_TypeChecker_Common.relation);
                                        FStar_TypeChecker_Common.rhs =
                                          (uu___149_5669.FStar_TypeChecker_Common.rhs);
                                        FStar_TypeChecker_Common.element =
                                          (uu___149_5669.FStar_TypeChecker_Common.element);
                                        FStar_TypeChecker_Common.logical_guard
                                          =
                                          (uu___149_5669.FStar_TypeChecker_Common.logical_guard);
                                        FStar_TypeChecker_Common.scope =
                                          (uu___149_5669.FStar_TypeChecker_Common.scope);
                                        FStar_TypeChecker_Common.reason =
                                          (uu___149_5669.FStar_TypeChecker_Common.reason);
                                        FStar_TypeChecker_Common.loc =
                                          (uu___149_5669.FStar_TypeChecker_Common.loc);
                                        FStar_TypeChecker_Common.rank =
                                          (uu___149_5669.FStar_TypeChecker_Common.rank)
                                      }  in
                                    (refine_flex, uu____5664)))
                      | (uu____5688,uu____5689) -> (rigid_rigid, tp)  in
                    (match uu____5480 with
                     | (rank,tp1) ->
                         let uu____5700 =
                           FStar_All.pipe_right
                             (let uu___150_5703 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___150_5703.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___150_5703.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___150_5703.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___150_5703.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___150_5703.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___150_5703.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.scope =
                                  (uu___150_5703.FStar_TypeChecker_Common.scope);
                                FStar_TypeChecker_Common.reason =
                                  (uu___150_5703.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___150_5703.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank = (Some rank)
                              })
                             (fun _0_43  ->
                                FStar_TypeChecker_Common.TProb _0_43)
                            in
                         (rank, uu____5700))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____5709 =
            FStar_All.pipe_right
              (let uu___151_5712 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___151_5712.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___151_5712.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___151_5712.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___151_5712.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___151_5712.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___151_5712.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.scope =
                   (uu___151_5712.FStar_TypeChecker_Common.scope);
                 FStar_TypeChecker_Common.reason =
                   (uu___151_5712.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___151_5712.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank = (Some rigid_rigid)
               }) (fun _0_44  -> FStar_TypeChecker_Common.CProb _0_44)
             in
          (rigid_rigid, uu____5709)
  
let next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob option * FStar_TypeChecker_Common.prob
      Prims.list * Prims.int)
  =
  fun wl  ->
    let rec aux uu____5744 probs =
      match uu____5744 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] -> (min1, out, min_rank)
           | hd1::tl1 ->
               let uu____5774 = rank wl hd1  in
               (match uu____5774 with
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
    match projectee with | UDeferred _0 -> true | uu____5842 -> false
  
let __proj__UDeferred__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let uu___is_USolved : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____5854 -> false
  
let __proj__USolved__item___0 : univ_eq_sol -> worklist =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let uu___is_UFailed : univ_eq_sol -> Prims.bool =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____5866 -> false
  
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
                        let uu____5903 = FStar_Syntax_Util.univ_kernel u3  in
                        match uu____5903 with
                        | (k,uu____5907) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Unionfind.equivalent v1 v2
                             | uu____5912 -> false)))
            | uu____5913 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
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
                        let uu____5956 =
                          really_solve_universe_eq pid_orig wl1 u13 u23  in
                        (match uu____5956 with
                         | USolved wl2 -> aux wl2 us12 us22
                         | failed -> failed)
                    | uu____5959 -> USolved wl1  in
                  aux wl us1 us2
                else
                  (let uu____5965 =
                     let uu____5966 = FStar_Syntax_Print.univ_to_string u12
                        in
                     let uu____5967 = FStar_Syntax_Print.univ_to_string u22
                        in
                     FStar_Util.format2
                       "Unable to unify universes: %s and %s" uu____5966
                       uu____5967
                      in
                   UFailed uu____5965)
            | (FStar_Syntax_Syntax.U_max us,u') ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____5983 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____5983 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | (u',FStar_Syntax_Syntax.U_max us) ->
                let rec aux wl1 us1 =
                  match us1 with
                  | [] -> USolved wl1
                  | u::us2 ->
                      let uu____6001 =
                        really_solve_universe_eq pid_orig wl1 u u'  in
                      (match uu____6001 with
                       | USolved wl2 -> aux wl2 us2
                       | failed -> failed)
                   in
                aux wl us
            | uu____6004 ->
                let uu____6007 =
                  let uu____6008 = FStar_Syntax_Print.univ_to_string u12  in
                  let uu____6009 = FStar_Syntax_Print.univ_to_string u22  in
                  FStar_Util.format3
                    "Unable to unify universes: %s and %s (%s)" uu____6008
                    uu____6009 msg
                   in
                UFailed uu____6007
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____6010,uu____6011) ->
              let uu____6012 =
                let uu____6013 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6014 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6013 uu____6014
                 in
              failwith uu____6012
          | (FStar_Syntax_Syntax.U_unknown ,uu____6015) ->
              let uu____6016 =
                let uu____6017 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6018 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6017 uu____6018
                 in
              failwith uu____6016
          | (uu____6019,FStar_Syntax_Syntax.U_bvar uu____6020) ->
              let uu____6021 =
                let uu____6022 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6023 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6022 uu____6023
                 in
              failwith uu____6021
          | (uu____6024,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____6025 =
                let uu____6026 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____6027 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____6026 uu____6027
                 in
              failwith uu____6025
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____6039 = FStar_Unionfind.equivalent v1 v2  in
              if uu____6039
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____6050 = occurs_univ v1 u3  in
              if uu____6050
              then
                let uu____6051 =
                  let uu____6052 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6053 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6052 uu____6053
                   in
                try_umax_components u11 u21 uu____6051
              else
                (let uu____6055 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6055)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____6063 = occurs_univ v1 u3  in
              if uu____6063
              then
                let uu____6064 =
                  let uu____6065 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____6066 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____6065 uu____6066
                   in
                try_umax_components u11 u21 uu____6064
              else
                (let uu____6068 = extend_solution pid_orig [UNIV (v1, u3)] wl
                    in
                 USolved uu____6068)
          | (FStar_Syntax_Syntax.U_max uu____6071,uu____6072) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6077 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6077
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____6079,FStar_Syntax_Syntax.U_max uu____6080) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____6085 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____6085
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____6087,FStar_Syntax_Syntax.U_zero
             ) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____6088,FStar_Syntax_Syntax.U_name
             uu____6089) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____6090) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____6091) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6092,FStar_Syntax_Syntax.U_succ
             uu____6093) -> UFailed "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____6094,FStar_Syntax_Syntax.U_zero
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
  let uu____6156 = bc1  in
  match uu____6156 with
  | (bs1,mk_cod1) ->
      let uu____6181 = bc2  in
      (match uu____6181 with
       | (bs2,mk_cod2) ->
           let curry n1 bs mk_cod =
             let uu____6228 = FStar_Util.first_N n1 bs  in
             match uu____6228 with
             | (bs3,rest) ->
                 let uu____6242 = mk_cod rest  in (bs3, uu____6242)
              in
           let l1 = FStar_List.length bs1  in
           let l2 = FStar_List.length bs2  in
           if l1 = l2
           then
             let uu____6260 =
               let uu____6264 = mk_cod1 []  in (bs1, uu____6264)  in
             let uu____6266 =
               let uu____6270 = mk_cod2 []  in (bs2, uu____6270)  in
             (uu____6260, uu____6266)
           else
             if l1 > l2
             then
               (let uu____6292 = curry l2 bs1 mk_cod1  in
                let uu____6299 =
                  let uu____6303 = mk_cod2 []  in (bs2, uu____6303)  in
                (uu____6292, uu____6299))
             else
               (let uu____6312 =
                  let uu____6316 = mk_cod1 []  in (bs1, uu____6316)  in
                let uu____6318 = curry l1 bs2 mk_cod2  in
                (uu____6312, uu____6318)))
  
let rec solve : FStar_TypeChecker_Env.env -> worklist -> solution =
  fun env  ->
    fun probs  ->
      (let uu____6422 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____6422
       then
         let uu____6423 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____6423
       else ());
      (let uu____6425 = next_prob probs  in
       match uu____6425 with
       | (Some hd1,tl1,rank1) ->
           let probs1 =
             let uu___152_6438 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___152_6438.wl_deferred);
               ctr = (uu___152_6438.ctr);
               defer_ok = (uu___152_6438.defer_ok);
               smt_ok = (uu___152_6438.smt_ok);
               tcenv = (uu___152_6438.tcenv)
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
                  let uu____6445 = solve_flex_rigid_join env tp probs1  in
                  (match uu____6445 with
                   | None  -> solve_t' env (maybe_invert tp) probs1
                   | Some wl -> solve env wl)
                else
                  if
                    ((Prims.op_Negation probs1.defer_ok) &&
                       (rigid_flex <= rank1))
                      && (rank1 <= refine_flex)
                  then
                    (let uu____6449 = solve_rigid_flex_meet env tp probs1  in
                     match uu____6449 with
                     | None  -> solve_t' env (maybe_invert tp) probs1
                     | Some wl -> solve env wl)
                  else solve_t' env (maybe_invert tp) probs1)
       | (None ,uu____6453,uu____6454) ->
           (match probs.wl_deferred with
            | [] -> Success []
            | uu____6463 ->
                let uu____6468 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____6496  ->
                          match uu____6496 with
                          | (c,uu____6501,uu____6502) -> c < probs.ctr))
                   in
                (match uu____6468 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____6524 =
                            FStar_List.map
                              (fun uu____6530  ->
                                 match uu____6530 with
                                 | (uu____6536,x,y) -> (x, y))
                              probs.wl_deferred
                             in
                          Success uu____6524
                      | uu____6539 ->
                          let uu____6544 =
                            let uu___153_6545 = probs  in
                            let uu____6546 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____6555  ->
                                      match uu____6555 with
                                      | (uu____6559,uu____6560,y) -> y))
                               in
                            {
                              attempting = uu____6546;
                              wl_deferred = rest;
                              ctr = (uu___153_6545.ctr);
                              defer_ok = (uu___153_6545.defer_ok);
                              smt_ok = (uu___153_6545.smt_ok);
                              tcenv = (uu___153_6545.tcenv)
                            }  in
                          solve env uu____6544))))

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
            let uu____6567 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____6567 with
            | USolved wl1 ->
                let uu____6569 = solve_prob orig None [] wl1  in
                solve env uu____6569
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
                  let uu____6603 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____6603 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____6606 -> UFailed "Unequal number of universes"  in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.tk = uu____6614;
                  FStar_Syntax_Syntax.pos = uu____6615;
                  FStar_Syntax_Syntax.vars = uu____6616;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.tk = uu____6619;
                  FStar_Syntax_Syntax.pos = uu____6620;
                  FStar_Syntax_Syntax.vars = uu____6621;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____6633,uu____6634) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____6639,FStar_Syntax_Syntax.Tm_uinst uu____6640) ->
                failwith "Impossible: expect head symbols to match"
            | uu____6645 -> USolved wl

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
            ((let uu____6653 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____6653
              then
                let uu____6654 = prob_to_string env orig  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____6654 msg
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and solve_rigid_flex_meet :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____6662 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____6662
         then
           let uu____6663 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by meeting refinements:%s\n"
             uu____6663
         else ());
        (let uu____6665 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs
            in
         match uu____6665 with
         | (u,args) ->
             let rec disjoin t1 t2 =
               let uu____6707 = head_matches_delta env () t1 t2  in
               match uu____6707 with
               | (mr,ts) ->
                   (match mr with
                    | MisMatch uu____6729 -> None
                    | FullMatch  ->
                        (match ts with
                         | None  -> Some (t1, [])
                         | Some (t11,t21) -> Some (t11, []))
                    | HeadMatch  ->
                        let uu____6755 =
                          match ts with
                          | Some (t11,t21) ->
                              let uu____6764 =
                                FStar_Syntax_Subst.compress t11  in
                              let uu____6765 =
                                FStar_Syntax_Subst.compress t21  in
                              (uu____6764, uu____6765)
                          | None  ->
                              let uu____6768 = FStar_Syntax_Subst.compress t1
                                 in
                              let uu____6769 = FStar_Syntax_Subst.compress t2
                                 in
                              (uu____6768, uu____6769)
                           in
                        (match uu____6755 with
                         | (t11,t21) ->
                             let eq_prob t12 t22 =
                               let uu____6791 =
                                 new_problem env t12
                                   FStar_TypeChecker_Common.EQ t22 None
                                   t12.FStar_Syntax_Syntax.pos
                                   "meeting refinements"
                                  in
                               FStar_All.pipe_left
                                 (fun _0_45  ->
                                    FStar_TypeChecker_Common.TProb _0_45)
                                 uu____6791
                                in
                             (match ((t11.FStar_Syntax_Syntax.n),
                                      (t21.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,phi1),FStar_Syntax_Syntax.Tm_refine
                                 (y,phi2)) ->
                                  let uu____6814 =
                                    let uu____6820 =
                                      let uu____6823 =
                                        let uu____6826 =
                                          let uu____6827 =
                                            let uu____6832 =
                                              FStar_Syntax_Util.mk_disj phi1
                                                phi2
                                               in
                                            (x, uu____6832)  in
                                          FStar_Syntax_Syntax.Tm_refine
                                            uu____6827
                                           in
                                        FStar_Syntax_Syntax.mk uu____6826  in
                                      uu____6823 None
                                        t11.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____6845 =
                                      let uu____6847 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          y.FStar_Syntax_Syntax.sort
                                         in
                                      [uu____6847]  in
                                    (uu____6820, uu____6845)  in
                                  Some uu____6814
                              | (uu____6856,FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6858)) ->
                                  let uu____6863 =
                                    let uu____6867 =
                                      let uu____6869 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t11
                                         in
                                      [uu____6869]  in
                                    (t11, uu____6867)  in
                                  Some uu____6863
                              | (FStar_Syntax_Syntax.Tm_refine
                                 (x,uu____6875),uu____6876) ->
                                  let uu____6881 =
                                    let uu____6885 =
                                      let uu____6887 =
                                        eq_prob x.FStar_Syntax_Syntax.sort
                                          t21
                                         in
                                      [uu____6887]  in
                                    (t21, uu____6885)  in
                                  Some uu____6881
                              | uu____6892 ->
                                  let uu____6895 =
                                    FStar_Syntax_Util.head_and_args t11  in
                                  (match uu____6895 with
                                   | (head1,uu____6910) ->
                                       let uu____6925 =
                                         let uu____6926 =
                                           FStar_Syntax_Util.un_uinst head1
                                            in
                                         uu____6926.FStar_Syntax_Syntax.n  in
                                       (match uu____6925 with
                                        | FStar_Syntax_Syntax.Tm_fvar
                                            {
                                              FStar_Syntax_Syntax.fv_name =
                                                uu____6933;
                                              FStar_Syntax_Syntax.fv_delta =
                                                FStar_Syntax_Syntax.Delta_defined_at_level
                                                i;
                                              FStar_Syntax_Syntax.fv_qual =
                                                uu____6935;_}
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
                                        | uu____6944 -> None)))))
                in
             let tt = u  in
             (match tt.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_uvar (uv,uu____6953) ->
                  let uu____6966 =
                    FStar_All.pipe_right wl.attempting
                      (FStar_List.partition
                         (fun uu___127_6975  ->
                            match uu___127_6975 with
                            | FStar_TypeChecker_Common.TProb tp1 ->
                                (match tp1.FStar_TypeChecker_Common.rank with
                                 | Some rank1 when is_rigid_flex rank1 ->
                                     let uu____6980 =
                                       FStar_Syntax_Util.head_and_args
                                         tp1.FStar_TypeChecker_Common.rhs
                                        in
                                     (match uu____6980 with
                                      | (u',uu____6991) ->
                                          let uu____7006 =
                                            let uu____7007 = whnf env u'  in
                                            uu____7007.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____7006 with
                                           | FStar_Syntax_Syntax.Tm_uvar
                                               (uv',uu____7011) ->
                                               FStar_Unionfind.equivalent uv
                                                 uv'
                                           | uu____7027 -> false))
                                 | uu____7028 -> false)
                            | uu____7030 -> false))
                     in
                  (match uu____6966 with
                   | (lower_bounds,rest) ->
                       let rec make_lower_bound uu____7051 tps =
                         match uu____7051 with
                         | (bound,sub_probs) ->
                             (match tps with
                              | [] -> Some (bound, sub_probs)
                              | (FStar_TypeChecker_Common.TProb hd1)::tl1 ->
                                  let uu____7078 =
                                    let uu____7083 =
                                      whnf env
                                        hd1.FStar_TypeChecker_Common.lhs
                                       in
                                    disjoin bound uu____7083  in
                                  (match uu____7078 with
                                   | Some (bound1,sub1) ->
                                       make_lower_bound
                                         (bound1,
                                           (FStar_List.append sub1 sub_probs))
                                         tl1
                                   | None  -> None)
                              | uu____7102 -> None)
                          in
                       let uu____7107 =
                         let uu____7112 =
                           let uu____7116 =
                             whnf env tp.FStar_TypeChecker_Common.lhs  in
                           (uu____7116, [])  in
                         make_lower_bound uu____7112 lower_bounds  in
                       (match uu____7107 with
                        | None  ->
                            ((let uu____7123 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7123
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
                            ((let uu____7136 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "RelCheck")
                                 in
                              if uu____7136
                              then
                                let wl' =
                                  let uu___154_7138 = wl  in
                                  {
                                    attempting =
                                      ((FStar_TypeChecker_Common.TProb
                                          eq_prob) :: sub_probs);
                                    wl_deferred = (uu___154_7138.wl_deferred);
                                    ctr = (uu___154_7138.ctr);
                                    defer_ok = (uu___154_7138.defer_ok);
                                    smt_ok = (uu___154_7138.smt_ok);
                                    tcenv = (uu___154_7138.tcenv)
                                  }  in
                                let uu____7139 = wl_to_string wl'  in
                                FStar_Util.print1
                                  "After meeting refinements: %s\n"
                                  uu____7139
                              else ());
                             (let uu____7141 =
                                solve_t env eq_prob
                                  (let uu___155_7142 = wl  in
                                   {
                                     attempting = sub_probs;
                                     wl_deferred =
                                       (uu___155_7142.wl_deferred);
                                     ctr = (uu___155_7142.ctr);
                                     defer_ok = (uu___155_7142.defer_ok);
                                     smt_ok = (uu___155_7142.smt_ok);
                                     tcenv = (uu___155_7142.tcenv)
                                   })
                                 in
                              match uu____7141 with
                              | Success uu____7144 ->
                                  let wl1 =
                                    let uu___156_7146 = wl  in
                                    {
                                      attempting = rest;
                                      wl_deferred =
                                        (uu___156_7146.wl_deferred);
                                      ctr = (uu___156_7146.ctr);
                                      defer_ok = (uu___156_7146.defer_ok);
                                      smt_ok = (uu___156_7146.smt_ok);
                                      tcenv = (uu___156_7146.tcenv)
                                    }  in
                                  let wl2 =
                                    solve_prob' false
                                      (FStar_TypeChecker_Common.TProb tp)
                                      None [] wl1
                                     in
                                  let uu____7148 =
                                    FStar_List.fold_left
                                      (fun wl3  ->
                                         fun p  ->
                                           solve_prob' true p None [] wl3)
                                      wl2 lower_bounds
                                     in
                                  Some wl2
                              | uu____7151 -> None))))
              | uu____7152 -> failwith "Impossible: Not a rigid-flex"))

and solve_flex_rigid_join :
  FStar_TypeChecker_Env.env -> tprob -> worklist -> worklist option =
  fun env  ->
    fun tp  ->
      fun wl  ->
        (let uu____7159 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelCheck")
            in
         if uu____7159
         then
           let uu____7160 =
             FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid  in
           FStar_Util.print1 "Trying to solve by joining refinements:%s\n"
             uu____7160
         else ());
        (let uu____7162 =
           FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
            in
         match uu____7162 with
         | (u,args) ->
             let uu____7189 =
               ((Prims.parse_int "0"), (Prims.parse_int "1"),
                 (Prims.parse_int "2"), (Prims.parse_int "3"),
                 (Prims.parse_int "4"))
                in
             (match uu____7189 with
              | (ok,head_match1,partial_match,fallback,failed_match) ->
                  let max1 i j = if i < j then j else i  in
                  let base_types_match t1 t2 =
                    let uu____7220 = FStar_Syntax_Util.head_and_args t1  in
                    match uu____7220 with
                    | (h1,args1) ->
                        let uu____7248 = FStar_Syntax_Util.head_and_args t2
                           in
                        (match uu____7248 with
                         | (h2,uu____7261) ->
                             (match ((h1.FStar_Syntax_Syntax.n),
                                      (h2.FStar_Syntax_Syntax.n))
                              with
                              | (FStar_Syntax_Syntax.Tm_fvar
                                 tc1,FStar_Syntax_Syntax.Tm_fvar tc2) ->
                                  let uu____7280 =
                                    FStar_Syntax_Syntax.fv_eq tc1 tc2  in
                                  if uu____7280
                                  then
                                    (if
                                       (FStar_List.length args1) =
                                         (Prims.parse_int "0")
                                     then Some []
                                     else
                                       (let uu____7293 =
                                          let uu____7295 =
                                            let uu____7296 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_46  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_46) uu____7296
                                             in
                                          [uu____7295]  in
                                        Some uu____7293))
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
                                       (let uu____7318 =
                                          let uu____7320 =
                                            let uu____7321 =
                                              new_problem env t1
                                                FStar_TypeChecker_Common.EQ
                                                t2 None
                                                t1.FStar_Syntax_Syntax.pos
                                                "joining refinements"
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_47  ->
                                                 FStar_TypeChecker_Common.TProb
                                                   _0_47) uu____7321
                                             in
                                          [uu____7320]  in
                                        Some uu____7318))
                                  else None
                              | uu____7329 -> None))
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
                             let uu____7395 =
                               let uu____7401 =
                                 let uu____7404 =
                                   FStar_Syntax_Util.mk_conj phi11 phi21  in
                                 FStar_Syntax_Util.refine x1 uu____7404  in
                               (uu____7401, m1)  in
                             Some uu____7395)
                    | (uu____7413,FStar_Syntax_Syntax.Tm_refine
                       (y,uu____7415)) ->
                        let m =
                          base_types_match t1 y.FStar_Syntax_Syntax.sort  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t2, m1))
                    | (FStar_Syntax_Syntax.Tm_refine
                       (x,uu____7447),uu____7448) ->
                        let m =
                          base_types_match x.FStar_Syntax_Syntax.sort t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                    | uu____7479 ->
                        let m = base_types_match t1 t2  in
                        (match m with
                         | None  -> None
                         | Some m1 -> Some (t1, m1))
                     in
                  let tt = u  in
                  (match tt.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar (uv,uu____7513) ->
                       let uu____7526 =
                         FStar_All.pipe_right wl.attempting
                           (FStar_List.partition
                              (fun uu___128_7535  ->
                                 match uu___128_7535 with
                                 | FStar_TypeChecker_Common.TProb tp1 ->
                                     (match tp1.FStar_TypeChecker_Common.rank
                                      with
                                      | Some rank1 when is_flex_rigid rank1
                                          ->
                                          let uu____7540 =
                                            FStar_Syntax_Util.head_and_args
                                              tp1.FStar_TypeChecker_Common.lhs
                                             in
                                          (match uu____7540 with
                                           | (u',uu____7551) ->
                                               let uu____7566 =
                                                 let uu____7567 = whnf env u'
                                                    in
                                                 uu____7567.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____7566 with
                                                | FStar_Syntax_Syntax.Tm_uvar
                                                    (uv',uu____7571) ->
                                                    FStar_Unionfind.equivalent
                                                      uv uv'
                                                | uu____7587 -> false))
                                      | uu____7588 -> false)
                                 | uu____7590 -> false))
                          in
                       (match uu____7526 with
                        | (upper_bounds,rest) ->
                            let rec make_upper_bound uu____7615 tps =
                              match uu____7615 with
                              | (bound,sub_probs) ->
                                  (match tps with
                                   | [] -> Some (bound, sub_probs)
                                   | (FStar_TypeChecker_Common.TProb
                                       hd1)::tl1 ->
                                       let uu____7656 =
                                         let uu____7663 =
                                           whnf env
                                             hd1.FStar_TypeChecker_Common.rhs
                                            in
                                         conjoin bound uu____7663  in
                                       (match uu____7656 with
                                        | Some (bound1,sub1) ->
                                            make_upper_bound
                                              (bound1,
                                                (FStar_List.append sub1
                                                   sub_probs)) tl1
                                        | None  -> None)
                                   | uu____7698 -> None)
                               in
                            let uu____7705 =
                              let uu____7712 =
                                let uu____7718 =
                                  whnf env tp.FStar_TypeChecker_Common.rhs
                                   in
                                (uu____7718, [])  in
                              make_upper_bound uu____7712 upper_bounds  in
                            (match uu____7705 with
                             | None  ->
                                 ((let uu____7727 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7727
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
                                 ((let uu____7746 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "RelCheck")
                                      in
                                   if uu____7746
                                   then
                                     let wl' =
                                       let uu___157_7748 = wl  in
                                       {
                                         attempting =
                                           ((FStar_TypeChecker_Common.TProb
                                               eq_prob) :: sub_probs);
                                         wl_deferred =
                                           (uu___157_7748.wl_deferred);
                                         ctr = (uu___157_7748.ctr);
                                         defer_ok = (uu___157_7748.defer_ok);
                                         smt_ok = (uu___157_7748.smt_ok);
                                         tcenv = (uu___157_7748.tcenv)
                                       }  in
                                     let uu____7749 = wl_to_string wl'  in
                                     FStar_Util.print1
                                       "After joining refinements: %s\n"
                                       uu____7749
                                   else ());
                                  (let uu____7751 =
                                     solve_t env eq_prob
                                       (let uu___158_7752 = wl  in
                                        {
                                          attempting = sub_probs;
                                          wl_deferred =
                                            (uu___158_7752.wl_deferred);
                                          ctr = (uu___158_7752.ctr);
                                          defer_ok = (uu___158_7752.defer_ok);
                                          smt_ok = (uu___158_7752.smt_ok);
                                          tcenv = (uu___158_7752.tcenv)
                                        })
                                      in
                                   match uu____7751 with
                                   | Success uu____7754 ->
                                       let wl1 =
                                         let uu___159_7756 = wl  in
                                         {
                                           attempting = rest;
                                           wl_deferred =
                                             (uu___159_7756.wl_deferred);
                                           ctr = (uu___159_7756.ctr);
                                           defer_ok =
                                             (uu___159_7756.defer_ok);
                                           smt_ok = (uu___159_7756.smt_ok);
                                           tcenv = (uu___159_7756.tcenv)
                                         }  in
                                       let wl2 =
                                         solve_prob' false
                                           (FStar_TypeChecker_Common.TProb tp)
                                           None [] wl1
                                          in
                                       let uu____7758 =
                                         FStar_List.fold_left
                                           (fun wl3  ->
                                              fun p  ->
                                                solve_prob' true p None []
                                                  wl3) wl2 upper_bounds
                                          in
                                       Some wl2
                                   | uu____7761 -> None))))
                   | uu____7762 -> failwith "Impossible: Not a flex-rigid")))

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
                    ((let uu____7827 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____7827
                      then
                        let uu____7828 = prob_to_string env1 rhs_prob  in
                        FStar_Util.print1 "rhs_prob = %s\n" uu____7828
                      else ());
                     (let formula =
                        FStar_All.pipe_right (p_guard rhs_prob)
                          FStar_Pervasives.fst
                         in
                      FStar_Util.Inl ([rhs_prob], formula)))
                | ((hd1,imp)::xs1,(hd2,imp')::ys1) when imp = imp' ->
                    let hd11 =
                      let uu___160_7860 = hd1  in
                      let uu____7861 =
                        FStar_Syntax_Subst.subst subst1
                          hd1.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___160_7860.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___160_7860.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7861
                      }  in
                    let hd21 =
                      let uu___161_7865 = hd2  in
                      let uu____7866 =
                        FStar_Syntax_Subst.subst subst1
                          hd2.FStar_Syntax_Syntax.sort
                         in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___161_7865.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___161_7865.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = uu____7866
                      }  in
                    let prob =
                      let uu____7870 =
                        let uu____7873 =
                          FStar_All.pipe_left invert_rel (p_rel orig)  in
                        mk_problem scope orig hd11.FStar_Syntax_Syntax.sort
                          uu____7873 hd21.FStar_Syntax_Syntax.sort None
                          "Formal parameter"
                         in
                      FStar_All.pipe_left
                        (fun _0_48  -> FStar_TypeChecker_Common.TProb _0_48)
                        uu____7870
                       in
                    let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                    let subst2 =
                      let uu____7881 =
                        FStar_Syntax_Subst.shift_subst (Prims.parse_int "1")
                          subst1
                         in
                      (FStar_Syntax_Syntax.DB ((Prims.parse_int "0"), hd12))
                        :: uu____7881
                       in
                    let env2 = FStar_TypeChecker_Env.push_bv env1 hd12  in
                    let uu____7884 =
                      aux ((hd12, imp) :: scope) env2 subst2 xs1 ys1  in
                    (match uu____7884 with
                     | FStar_Util.Inl (sub_probs,phi) ->
                         let phi1 =
                           let uu____7902 =
                             FStar_All.pipe_right (p_guard prob)
                               FStar_Pervasives.fst
                              in
                           let uu____7905 =
                             close_forall env2 [(hd12, imp)] phi  in
                           FStar_Syntax_Util.mk_conj uu____7902 uu____7905
                            in
                         ((let uu____7911 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env2)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____7911
                           then
                             let uu____7912 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____7913 =
                               FStar_Syntax_Print.bv_to_string hd12  in
                             FStar_Util.print2 "Formula is %s\n\thd1=%s\n"
                               uu____7912 uu____7913
                           else ());
                          FStar_Util.Inl ((prob :: sub_probs), phi1))
                     | fail -> fail)
                | uu____7928 ->
                    FStar_Util.Inr "arity or argument-qualifier mismatch"
                 in
              let scope = p_scope orig  in
              let uu____7934 = aux scope env [] bs1 bs2  in
              match uu____7934 with
              | FStar_Util.Inr msg -> giveup env msg orig
              | FStar_Util.Inl (sub_probs,phi) ->
                  let wl1 = solve_prob orig (Some phi) [] wl  in
                  solve env (attempt sub_probs wl1)

and solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let uu____7950 = compress_tprob wl problem  in
        solve_t' env uu____7950 wl

and solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
        let rigid_rigid_delta env1 orig wl1 head1 head2 t1 t2 =
          let uu____7983 = head_matches_delta env1 wl1 t1 t2  in
          match uu____7983 with
          | (m,o) ->
              (match (m, o) with
               | (MisMatch uu____8000,uu____8001) ->
                   let may_relate head3 =
                     let uu____8016 =
                       let uu____8017 = FStar_Syntax_Util.un_uinst head3  in
                       uu____8017.FStar_Syntax_Syntax.n  in
                     match uu____8016 with
                     | FStar_Syntax_Syntax.Tm_name uu____8020 -> true
                     | FStar_Syntax_Syntax.Tm_match uu____8021 -> true
                     | FStar_Syntax_Syntax.Tm_fvar tc ->
                         tc.FStar_Syntax_Syntax.fv_delta =
                           FStar_Syntax_Syntax.Delta_equational
                     | uu____8038 -> false  in
                   let uu____8039 =
                     ((may_relate head1) || (may_relate head2)) && wl1.smt_ok
                      in
                   if uu____8039
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
                                let uu____8056 =
                                  let uu____8057 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_Syntax_Util.mk_has_type t11
                                    uu____8057 t21
                                   in
                                FStar_Syntax_Util.mk_forall u_x x uu____8056
                             in
                          if
                            problem.FStar_TypeChecker_Common.relation =
                              FStar_TypeChecker_Common.SUB
                          then has_type_guard t1 t2
                          else has_type_guard t2 t1)
                        in
                     let uu____8059 = solve_prob orig (Some guard) [] wl1  in
                     solve env1 uu____8059
                   else giveup env1 "head mismatch" orig
               | (uu____8061,Some (t11,t21)) ->
                   solve_t env1
                     (let uu___162_8069 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___162_8069.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___162_8069.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___162_8069.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___162_8069.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___162_8069.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___162_8069.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___162_8069.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___162_8069.FStar_TypeChecker_Common.rank)
                      }) wl1
               | (uu____8070,None ) ->
                   ((let uu____8077 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8077
                     then
                       let uu____8078 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____8079 = FStar_Syntax_Print.tag_of_term t1  in
                       let uu____8080 = FStar_Syntax_Print.term_to_string t2
                          in
                       let uu____8081 = FStar_Syntax_Print.tag_of_term t2  in
                       FStar_Util.print4
                         "Head matches: %s (%s) and %s (%s)\n" uu____8078
                         uu____8079 uu____8080 uu____8081
                     else ());
                    (let uu____8083 = FStar_Syntax_Util.head_and_args t1  in
                     match uu____8083 with
                     | (head11,args1) ->
                         let uu____8109 = FStar_Syntax_Util.head_and_args t2
                            in
                         (match uu____8109 with
                          | (head21,args2) ->
                              let nargs = FStar_List.length args1  in
                              if nargs <> (FStar_List.length args2)
                              then
                                let uu____8149 =
                                  let uu____8150 =
                                    FStar_Syntax_Print.term_to_string head11
                                     in
                                  let uu____8151 = args_to_string args1  in
                                  let uu____8152 =
                                    FStar_Syntax_Print.term_to_string head21
                                     in
                                  let uu____8153 = args_to_string args2  in
                                  FStar_Util.format4
                                    "unequal number of arguments: %s[%s] and %s[%s]"
                                    uu____8150 uu____8151 uu____8152
                                    uu____8153
                                   in
                                giveup env1 uu____8149 orig
                              else
                                (let uu____8155 =
                                   (nargs = (Prims.parse_int "0")) ||
                                     (let uu____8158 =
                                        FStar_Syntax_Util.eq_args args1 args2
                                         in
                                      uu____8158 = FStar_Syntax_Util.Equal)
                                    in
                                 if uu____8155
                                 then
                                   let uu____8159 =
                                     solve_maybe_uinsts env1 orig head11
                                       head21 wl1
                                      in
                                   match uu____8159 with
                                   | USolved wl2 ->
                                       let uu____8161 =
                                         solve_prob orig None [] wl2  in
                                       solve env1 uu____8161
                                   | UFailed msg -> giveup env1 msg orig
                                   | UDeferred wl2 ->
                                       solve env1
                                         (defer "universe constraints" orig
                                            wl2)
                                 else
                                   (let uu____8165 =
                                      base_and_refinement env1 wl1 t1  in
                                    match uu____8165 with
                                    | (base1,refinement1) ->
                                        let uu____8191 =
                                          base_and_refinement env1 wl1 t2  in
                                        (match uu____8191 with
                                         | (base2,refinement2) ->
                                             (match (refinement1,
                                                      refinement2)
                                              with
                                              | (None ,None ) ->
                                                  let uu____8245 =
                                                    solve_maybe_uinsts env1
                                                      orig head11 head21 wl1
                                                     in
                                                  (match uu____8245 with
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
                                                           (fun uu____8255 
                                                              ->
                                                              fun uu____8256 
                                                                ->
                                                                match 
                                                                  (uu____8255,
                                                                    uu____8256)
                                                                with
                                                                | ((a,uu____8266),
                                                                   (a',uu____8268))
                                                                    ->
                                                                    let uu____8273
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
                                                                    _0_49  ->
                                                                    FStar_TypeChecker_Common.TProb
                                                                    _0_49)
                                                                    uu____8273)
                                                           args1 args2
                                                          in
                                                       let formula =
                                                         let uu____8279 =
                                                           FStar_List.map
                                                             (fun p  ->
                                                                fst
                                                                  (p_guard p))
                                                             subprobs
                                                            in
                                                         FStar_Syntax_Util.mk_conj_l
                                                           uu____8279
                                                          in
                                                       let wl3 =
                                                         solve_prob orig
                                                           (Some formula) []
                                                           wl2
                                                          in
                                                       solve env1
                                                         (attempt subprobs
                                                            wl3))
                                              | uu____8283 ->
                                                  let lhs =
                                                    force_refinement
                                                      (base1, refinement1)
                                                     in
                                                  let rhs =
                                                    force_refinement
                                                      (base2, refinement2)
                                                     in
                                                  solve_t env1
                                                    (let uu___163_8316 =
                                                       problem  in
                                                     {
                                                       FStar_TypeChecker_Common.pid
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.pid);
                                                       FStar_TypeChecker_Common.lhs
                                                         = lhs;
                                                       FStar_TypeChecker_Common.relation
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.relation);
                                                       FStar_TypeChecker_Common.rhs
                                                         = rhs;
                                                       FStar_TypeChecker_Common.element
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.element);
                                                       FStar_TypeChecker_Common.logical_guard
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.logical_guard);
                                                       FStar_TypeChecker_Common.scope
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.scope);
                                                       FStar_TypeChecker_Common.reason
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.reason);
                                                       FStar_TypeChecker_Common.loc
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.loc);
                                                       FStar_TypeChecker_Common.rank
                                                         =
                                                         (uu___163_8316.FStar_TypeChecker_Common.rank)
                                                     }) wl1))))))))
           in
        let imitate orig env1 wl1 p =
          let uu____8336 = p  in
          match uu____8336 with
          | (((u,k),xs,c),ps,(h,uu____8347,qs)) ->
              let xs1 = sn_binders env1 xs  in
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8396 = imitation_sub_probs orig env1 xs1 ps qs  in
              (match uu____8396 with
               | (sub_probs,gs_xs,formula) ->
                   let im =
                     let uu____8410 = h gs_xs  in
                     let uu____8411 =
                       let uu____8418 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lcomp_of_comp c)
                           (fun _0_50  -> FStar_Util.Inl _0_50)
                          in
                       FStar_All.pipe_right uu____8418
                         (fun _0_51  -> Some _0_51)
                        in
                     FStar_Syntax_Util.abs xs1 uu____8410 uu____8411  in
                   ((let uu____8449 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____8449
                     then
                       let uu____8450 =
                         FStar_Syntax_Print.binders_to_string ", " xs1  in
                       let uu____8451 = FStar_Syntax_Print.comp_to_string c
                          in
                       let uu____8452 = FStar_Syntax_Print.term_to_string im
                          in
                       let uu____8453 = FStar_Syntax_Print.tag_of_term im  in
                       let uu____8454 =
                         let uu____8455 =
                           FStar_List.map (prob_to_string env1) sub_probs  in
                         FStar_All.pipe_right uu____8455
                           (FStar_String.concat ", ")
                          in
                       let uu____8458 =
                         FStar_TypeChecker_Normalize.term_to_string env1
                           formula
                          in
                       FStar_Util.print6
                         "Imitating  binders are {%s}, comp=%s\n\t%s (%s)\nsub_probs = %s\nformula=%s\n"
                         uu____8450 uu____8451 uu____8452 uu____8453
                         uu____8454 uu____8458
                     else ());
                    (let wl2 =
                       solve_prob orig (Some formula) [TERM ((u, k), im)] wl1
                        in
                     solve env1 (attempt sub_probs wl2))))
           in
        let imitate' orig env1 wl1 uu___129_8476 =
          match uu___129_8476 with
          | None  -> giveup env1 "unable to compute subterms" orig
          | Some p -> imitate orig env1 wl1 p  in
        let project orig env1 wl1 i p =
          let uu____8505 = p  in
          match uu____8505 with
          | ((u,xs,c),ps,(h,matches,qs)) ->
              let r = FStar_TypeChecker_Env.get_range env1  in
              let uu____8563 = FStar_List.nth ps i  in
              (match uu____8563 with
               | (pi,uu____8566) ->
                   let uu____8571 = FStar_List.nth xs i  in
                   (match uu____8571 with
                    | (xi,uu____8578) ->
                        let rec gs k =
                          let uu____8587 = FStar_Syntax_Util.arrow_formals k
                             in
                          match uu____8587 with
                          | (bs,k1) ->
                              let rec aux subst1 bs1 =
                                match bs1 with
                                | [] -> ([], [])
                                | (a,uu____8639)::tl1 ->
                                    let k_a =
                                      FStar_Syntax_Subst.subst subst1
                                        a.FStar_Syntax_Syntax.sort
                                       in
                                    let uu____8647 = new_uvar r xs k_a  in
                                    (match uu____8647 with
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
                                         let uu____8666 = aux subst2 tl1  in
                                         (match uu____8666 with
                                          | (gi_xs',gi_ps') ->
                                              let uu____8681 =
                                                let uu____8683 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_xs1
                                                   in
                                                uu____8683 :: gi_xs'  in
                                              let uu____8684 =
                                                let uu____8686 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    gi_ps
                                                   in
                                                uu____8686 :: gi_ps'  in
                                              (uu____8681, uu____8684)))
                                 in
                              aux [] bs
                           in
                        let uu____8689 =
                          let uu____8690 = matches pi  in
                          FStar_All.pipe_left Prims.op_Negation uu____8690
                           in
                        if uu____8689
                        then None
                        else
                          (let uu____8693 = gs xi.FStar_Syntax_Syntax.sort
                              in
                           match uu____8693 with
                           | (g_xs,uu____8700) ->
                               let xi1 = FStar_Syntax_Syntax.bv_to_name xi
                                  in
                               let proj =
                                 let uu____8707 =
                                   (FStar_Syntax_Syntax.mk_Tm_app xi1 g_xs)
                                     None r
                                    in
                                 let uu____8712 =
                                   let uu____8719 =
                                     FStar_All.pipe_right
                                       (FStar_Syntax_Util.lcomp_of_comp c)
                                       (fun _0_52  -> FStar_Util.Inl _0_52)
                                      in
                                   FStar_All.pipe_right uu____8719
                                     (fun _0_53  -> Some _0_53)
                                    in
                                 FStar_Syntax_Util.abs xs uu____8707
                                   uu____8712
                                  in
                               let sub1 =
                                 let uu____8750 =
                                   let uu____8753 =
                                     (FStar_Syntax_Syntax.mk_Tm_app proj ps)
                                       None r
                                      in
                                   let uu____8760 =
                                     let uu____8763 =
                                       FStar_List.map
                                         (fun uu____8769  ->
                                            match uu____8769 with
                                            | (uu____8774,uu____8775,y) -> y)
                                         qs
                                        in
                                     FStar_All.pipe_left h uu____8763  in
                                   mk_problem (p_scope orig) orig uu____8753
                                     (p_rel orig) uu____8760 None
                                     "projection"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_54  ->
                                      FStar_TypeChecker_Common.TProb _0_54)
                                   uu____8750
                                  in
                               ((let uu____8785 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____8785
                                 then
                                   let uu____8786 =
                                     FStar_Syntax_Print.term_to_string proj
                                      in
                                   let uu____8787 = prob_to_string env1 sub1
                                      in
                                   FStar_Util.print2
                                     "Projecting %s\n\tsubprob=%s\n"
                                     uu____8786 uu____8787
                                 else ());
                                (let wl2 =
                                   let uu____8790 =
                                     let uu____8792 =
                                       FStar_All.pipe_left
                                         FStar_Pervasives.fst (p_guard sub1)
                                        in
                                     Some uu____8792  in
                                   solve_prob orig uu____8790
                                     [TERM (u, proj)] wl1
                                    in
                                 let uu____8797 =
                                   solve env1 (attempt [sub1] wl2)  in
                                 FStar_All.pipe_left
                                   (fun _0_55  -> Some _0_55) uu____8797)))))
           in
        let solve_t_flex_rigid patterns_only orig lhs t2 wl1 =
          let uu____8821 = lhs  in
          match uu____8821 with
          | ((t1,uv,k_uv,args_lhs),maybe_pat_vars) ->
              let subterms ps =
                let uu____8844 = FStar_Syntax_Util.arrow_formals_comp k_uv
                   in
                match uu____8844 with
                | (xs,c) ->
                    if (FStar_List.length xs) = (FStar_List.length ps)
                    then
                      let uu____8866 =
                        let uu____8892 = decompose env t2  in
                        (((uv, k_uv), xs, c), ps, uu____8892)  in
                      Some uu____8866
                    else
                      (let k_uv1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env k_uv
                          in
                       let rec elim k args =
                         let uu____8975 =
                           let uu____8979 =
                             let uu____8980 = FStar_Syntax_Subst.compress k
                                in
                             uu____8980.FStar_Syntax_Syntax.n  in
                           (uu____8979, args)  in
                         match uu____8975 with
                         | (uu____8987,[]) ->
                             let uu____8989 =
                               let uu____8995 =
                                 FStar_Syntax_Syntax.mk_Total k  in
                               ([], uu____8995)  in
                             Some uu____8989
                         | (FStar_Syntax_Syntax.Tm_uvar
                            uu____9006,uu____9007) ->
                             let uu____9018 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9018 with
                              | (uv1,uv_args) ->
                                  let uu____9047 =
                                    let uu____9048 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9048.FStar_Syntax_Syntax.n  in
                                  (match uu____9047 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9055) ->
                                       let uu____9068 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9068 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9082  ->
                                                      let uu____9083 =
                                                        let uu____9084 =
                                                          let uu____9085 =
                                                            let uu____9088 =
                                                              let uu____9089
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9089
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9088
                                                             in
                                                          fst uu____9085  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9084
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9083))
                                               in
                                            let c1 =
                                              let uu____9095 =
                                                let uu____9096 =
                                                  let uu____9099 =
                                                    let uu____9100 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9100
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9099
                                                   in
                                                fst uu____9096  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9095
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9109 =
                                                let uu____9116 =
                                                  let uu____9122 =
                                                    let uu____9123 =
                                                      let uu____9126 =
                                                        let uu____9127 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9127
                                                          FStar_Pervasives.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9126
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9123
                                                     in
                                                  FStar_Util.Inl uu____9122
                                                   in
                                                Some uu____9116  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9109
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9150 -> None))
                         | (FStar_Syntax_Syntax.Tm_app uu____9153,uu____9154)
                             ->
                             let uu____9166 =
                               FStar_Syntax_Util.head_and_args k  in
                             (match uu____9166 with
                              | (uv1,uv_args) ->
                                  let uu____9195 =
                                    let uu____9196 =
                                      FStar_Syntax_Subst.compress uv1  in
                                    uu____9196.FStar_Syntax_Syntax.n  in
                                  (match uu____9195 with
                                   | FStar_Syntax_Syntax.Tm_uvar
                                       (uvar,uu____9203) ->
                                       let uu____9216 =
                                         pat_vars env [] uv_args  in
                                       (match uu____9216 with
                                        | None  -> None
                                        | Some scope ->
                                            let xs1 =
                                              FStar_All.pipe_right args
                                                (FStar_List.map
                                                   (fun uu____9230  ->
                                                      let uu____9231 =
                                                        let uu____9232 =
                                                          let uu____9233 =
                                                            let uu____9236 =
                                                              let uu____9237
                                                                =
                                                                FStar_Syntax_Util.type_u
                                                                  ()
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____9237
                                                                FStar_Pervasives.fst
                                                               in
                                                            new_uvar
                                                              k.FStar_Syntax_Syntax.pos
                                                              scope
                                                              uu____9236
                                                             in
                                                          fst uu____9233  in
                                                        FStar_Syntax_Syntax.new_bv
                                                          (Some
                                                             (k.FStar_Syntax_Syntax.pos))
                                                          uu____9232
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Syntax.mk_binder
                                                        uu____9231))
                                               in
                                            let c1 =
                                              let uu____9243 =
                                                let uu____9244 =
                                                  let uu____9247 =
                                                    let uu____9248 =
                                                      FStar_Syntax_Util.type_u
                                                        ()
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____9248
                                                      FStar_Pervasives.fst
                                                     in
                                                  new_uvar
                                                    k.FStar_Syntax_Syntax.pos
                                                    scope uu____9247
                                                   in
                                                fst uu____9244  in
                                              FStar_Syntax_Syntax.mk_Total
                                                uu____9243
                                               in
                                            let k' =
                                              FStar_Syntax_Util.arrow xs1 c1
                                               in
                                            let uv_sol =
                                              let uu____9257 =
                                                let uu____9264 =
                                                  let uu____9270 =
                                                    let uu____9271 =
                                                      let uu____9274 =
                                                        let uu____9275 =
                                                          FStar_Syntax_Util.type_u
                                                            ()
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____9275
                                                          FStar_Pervasives.fst
                                                         in
                                                      FStar_Syntax_Syntax.mk_Total
                                                        uu____9274
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_Syntax_Util.lcomp_of_comp
                                                      uu____9271
                                                     in
                                                  FStar_Util.Inl uu____9270
                                                   in
                                                Some uu____9264  in
                                              FStar_Syntax_Util.abs scope k'
                                                uu____9257
                                               in
                                            (FStar_Unionfind.change uvar
                                               (FStar_Syntax_Syntax.Fixed
                                                  uv_sol);
                                             Some (xs1, c1)))
                                   | uu____9298 -> None))
                         | (FStar_Syntax_Syntax.Tm_arrow (xs1,c1),uu____9303)
                             ->
                             let n_args = FStar_List.length args  in
                             let n_xs = FStar_List.length xs1  in
                             if n_xs = n_args
                             then
                               let uu____9329 =
                                 FStar_Syntax_Subst.open_comp xs1 c1  in
                               FStar_All.pipe_right uu____9329
                                 (fun _0_56  -> Some _0_56)
                             else
                               if n_xs < n_args
                               then
                                 (let uu____9348 =
                                    FStar_Util.first_N n_xs args  in
                                  match uu____9348 with
                                  | (args1,rest) ->
                                      let uu____9364 =
                                        FStar_Syntax_Subst.open_comp xs1 c1
                                         in
                                      (match uu____9364 with
                                       | (xs2,c2) ->
                                           let uu____9372 =
                                             elim
                                               (FStar_Syntax_Util.comp_result
                                                  c2) rest
                                              in
                                           FStar_Util.bind_opt uu____9372
                                             (fun uu____9383  ->
                                                match uu____9383 with
                                                | (xs',c3) ->
                                                    Some
                                                      ((FStar_List.append xs2
                                                          xs'), c3))))
                               else
                                 (let uu____9405 =
                                    FStar_Util.first_N n_args xs1  in
                                  match uu____9405 with
                                  | (xs2,rest) ->
                                      let t =
                                        (FStar_Syntax_Syntax.mk
                                           (FStar_Syntax_Syntax.Tm_arrow
                                              (rest, c1))) None
                                          k.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____9451 =
                                        let uu____9454 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        FStar_Syntax_Subst.open_comp xs2
                                          uu____9454
                                         in
                                      FStar_All.pipe_right uu____9451
                                        (fun _0_57  -> Some _0_57))
                         | uu____9462 ->
                             let uu____9466 =
                               let uu____9467 =
                                 FStar_Syntax_Print.uvar_to_string uv  in
                               let uu____9471 =
                                 FStar_Syntax_Print.term_to_string k  in
                               let uu____9472 =
                                 FStar_Syntax_Print.term_to_string k_uv1  in
                               FStar_Util.format3
                                 "Impossible: ill-typed application %s : %s\n\t%s"
                                 uu____9467 uu____9471 uu____9472
                                in
                             failwith uu____9466
                          in
                       let uu____9476 = elim k_uv1 ps  in
                       FStar_Util.bind_opt uu____9476
                         (fun uu____9504  ->
                            match uu____9504 with
                            | (xs1,c1) ->
                                let uu____9532 =
                                  let uu____9555 = decompose env t2  in
                                  (((uv, k_uv1), xs1, c1), ps, uu____9555)
                                   in
                                Some uu____9532))
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
                     let uu____9627 = imitate orig env wl1 st  in
                     match uu____9627 with
                     | Failed uu____9632 ->
                         (FStar_Unionfind.rollback tx;
                          imitate_or_project n1 stopt
                            (i + (Prims.parse_int "1")))
                     | sol -> sol
                   else
                     (let uu____9638 = project orig env wl1 i st  in
                      match uu____9638 with
                      | None  ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some (Failed uu____9645) ->
                          (FStar_Unionfind.rollback tx;
                           imitate_or_project n1 stopt
                             (i + (Prims.parse_int "1")))
                      | Some sol -> sol))
                 in
              let check_head fvs1 t21 =
                let uu____9659 = FStar_Syntax_Util.head_and_args t21  in
                match uu____9659 with
                | (hd1,uu____9670) ->
                    (match hd1.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_arrow uu____9685 -> true
                     | FStar_Syntax_Syntax.Tm_constant uu____9693 -> true
                     | FStar_Syntax_Syntax.Tm_abs uu____9694 -> true
                     | uu____9709 ->
                         let fvs_hd = FStar_Syntax_Free.names hd1  in
                         let uu____9712 =
                           FStar_Util.set_is_subset_of fvs_hd fvs1  in
                         if uu____9712
                         then true
                         else
                           ((let uu____9715 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____9715
                             then
                               let uu____9716 = names_to_string fvs_hd  in
                               FStar_Util.print1 "Free variables are %s"
                                 uu____9716
                             else ());
                            false))
                 in
              let imitate_ok t21 =
                let fvs_hd =
                  let uu____9724 =
                    let uu____9727 = FStar_Syntax_Util.head_and_args t21  in
                    FStar_All.pipe_right uu____9727 FStar_Pervasives.fst  in
                  FStar_All.pipe_right uu____9724 FStar_Syntax_Free.names  in
                let uu____9758 = FStar_Util.set_is_empty fvs_hd  in
                if uu____9758
                then ~- (Prims.parse_int "1")
                else (Prims.parse_int "0")  in
              (match maybe_pat_vars with
               | Some vars ->
                   let t11 = sn env t1  in
                   let t21 = sn env t2  in
                   let fvs1 = FStar_Syntax_Free.names t11  in
                   let fvs2 = FStar_Syntax_Free.names t21  in
                   let uu____9767 = occurs_check env wl1 (uv, k_uv) t21  in
                   (match uu____9767 with
                    | (occurs_ok,msg) ->
                        if Prims.op_Negation occurs_ok
                        then
                          let uu____9775 =
                            let uu____9776 = FStar_Option.get msg  in
                            Prims.strcat "occurs-check failed: " uu____9776
                             in
                          giveup_or_defer1 orig uu____9775
                        else
                          (let uu____9778 =
                             FStar_Util.set_is_subset_of fvs2 fvs1  in
                           if uu____9778
                           then
                             let uu____9779 =
                               ((Prims.op_Negation patterns_only) &&
                                  (FStar_Syntax_Util.is_function_typ t21))
                                 &&
                                 ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
                                in
                             (if uu____9779
                              then
                                let uu____9780 = subterms args_lhs  in
                                imitate' orig env wl1 uu____9780
                              else
                                ((let uu____9784 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____9784
                                  then
                                    let uu____9785 =
                                      FStar_Syntax_Print.term_to_string t11
                                       in
                                    let uu____9786 = names_to_string fvs1  in
                                    let uu____9787 = names_to_string fvs2  in
                                    FStar_Util.print3
                                      "Pattern %s with fvars=%s succeeded fvar check: %s\n"
                                      uu____9785 uu____9786 uu____9787
                                  else ());
                                 (let sol =
                                    match vars with
                                    | [] -> t21
                                    | uu____9792 ->
                                        let uu____9793 = sn_binders env vars
                                           in
                                        u_abs k_uv uu____9793 t21
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
                               (let uu____9802 =
                                  (Prims.op_Negation patterns_only) &&
                                    (check_head fvs1 t21)
                                   in
                                if uu____9802
                                then
                                  ((let uu____9804 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "Rel")
                                       in
                                    if uu____9804
                                    then
                                      let uu____9805 =
                                        FStar_Syntax_Print.term_to_string t11
                                         in
                                      let uu____9806 = names_to_string fvs1
                                         in
                                      let uu____9807 = names_to_string fvs2
                                         in
                                      FStar_Util.print3
                                        "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n"
                                        uu____9805 uu____9806 uu____9807
                                    else ());
                                   (let uu____9809 = subterms args_lhs  in
                                    imitate_or_project
                                      (FStar_List.length args_lhs) uu____9809
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
                     (let uu____9820 =
                        let uu____9821 = FStar_Syntax_Free.names t1  in
                        check_head uu____9821 t2  in
                      if uu____9820
                      then
                        let im_ok = imitate_ok t2  in
                        ((let uu____9825 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "Rel")
                             in
                          if uu____9825
                          then
                            let uu____9826 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not a pattern (%s) ... %s\n"
                              uu____9826
                              (if im_ok < (Prims.parse_int "0")
                               then "imitating"
                               else "projecting")
                          else ());
                         (let uu____9829 = subterms args_lhs  in
                          imitate_or_project (FStar_List.length args_lhs)
                            uu____9829 im_ok))
                      else giveup env "head-symbol is free" orig))
           in
        let flex_flex1 orig lhs rhs =
          if wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)
          then solve env (defer "flex-flex deferred" orig wl)
          else
            (let force_quasi_pattern xs_opt uu____9871 =
               match uu____9871 with
               | (t,u,k,args) ->
                   let uu____9901 = FStar_Syntax_Util.arrow_formals k  in
                   (match uu____9901 with
                    | (all_formals,uu____9912) ->
                        let rec aux pat_args pattern_vars pattern_var_set
                          formals args1 =
                          match (formals, args1) with
                          | ([],[]) ->
                              let pat_args1 =
                                FStar_All.pipe_right
                                  (FStar_List.rev pat_args)
                                  (FStar_List.map
                                     (fun uu____10004  ->
                                        match uu____10004 with
                                        | (x,imp) ->
                                            let uu____10011 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            (uu____10011, imp)))
                                 in
                              let pattern_vars1 = FStar_List.rev pattern_vars
                                 in
                              let kk =
                                let uu____10019 = FStar_Syntax_Util.type_u ()
                                   in
                                match uu____10019 with
                                | (t1,uu____10023) ->
                                    let uu____10024 =
                                      new_uvar t1.FStar_Syntax_Syntax.pos
                                        pattern_vars1 t1
                                       in
                                    fst uu____10024
                                 in
                              let uu____10027 =
                                new_uvar t.FStar_Syntax_Syntax.pos
                                  pattern_vars1 kk
                                 in
                              (match uu____10027 with
                               | (t',tm_u1) ->
                                   let uu____10034 = destruct_flex_t t'  in
                                   (match uu____10034 with
                                    | (uu____10054,u1,k1,uu____10057) ->
                                        let sol =
                                          let uu____10085 =
                                            let uu____10090 =
                                              u_abs k all_formals t'  in
                                            ((u, k), uu____10090)  in
                                          TERM uu____10085  in
                                        let t_app =
                                          (FStar_Syntax_Syntax.mk_Tm_app
                                             tm_u1 pat_args1) None
                                            t.FStar_Syntax_Syntax.pos
                                           in
                                        (sol, (t_app, u1, k1, pat_args1))))
                          | (formal::formals1,hd1::tl1) ->
                              let uu____10150 = pat_var_opt env pat_args hd1
                                 in
                              (match uu____10150 with
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
                                              (fun uu____10179  ->
                                                 match uu____10179 with
                                                 | (x,uu____10183) ->
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
                                      let uu____10189 =
                                        let uu____10190 =
                                          FStar_Util.set_is_subset_of fvs
                                            pattern_var_set
                                           in
                                        Prims.op_Negation uu____10190  in
                                      if uu____10189
                                      then
                                        aux pat_args pattern_vars
                                          pattern_var_set formals1 tl1
                                      else
                                        (let uu____10194 =
                                           FStar_Util.set_add (fst formal)
                                             pattern_var_set
                                            in
                                         aux (y :: pat_args) (formal ::
                                           pattern_vars) uu____10194 formals1
                                           tl1)))
                          | uu____10200 -> failwith "Impossible"  in
                        let uu____10211 = FStar_Syntax_Syntax.new_bv_set ()
                           in
                        aux [] [] uu____10211 all_formals args)
                in
             let solve_both_pats wl1 uu____10259 uu____10260 r =
               match (uu____10259, uu____10260) with
               | ((u1,k1,xs,args1),(u2,k2,ys,args2)) ->
                   let uu____10414 =
                     (FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)
                      in
                   if uu____10414
                   then
                     let uu____10418 = solve_prob orig None [] wl1  in
                     solve env uu____10418
                   else
                     (let xs1 = sn_binders env xs  in
                      let ys1 = sn_binders env ys  in
                      let zs = intersect_vars xs1 ys1  in
                      (let uu____10433 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____10433
                       then
                         let uu____10434 =
                           FStar_Syntax_Print.binders_to_string ", " xs1  in
                         let uu____10435 =
                           FStar_Syntax_Print.binders_to_string ", " ys1  in
                         let uu____10436 =
                           FStar_Syntax_Print.binders_to_string ", " zs  in
                         let uu____10437 =
                           FStar_Syntax_Print.term_to_string k1  in
                         let uu____10438 =
                           FStar_Syntax_Print.term_to_string k2  in
                         FStar_Util.print5
                           "Flex-flex patterns: intersected %s and %s; got %s\n\tk1=%s\n\tk2=%s\n"
                           uu____10434 uu____10435 uu____10436 uu____10437
                           uu____10438
                       else ());
                      (let subst_k k xs2 args =
                         let xs_len = FStar_List.length xs2  in
                         let args_len = FStar_List.length args  in
                         if xs_len = args_len
                         then
                           let uu____10480 =
                             FStar_Syntax_Util.subst_of_list xs2 args  in
                           FStar_Syntax_Subst.subst uu____10480 k
                         else
                           if args_len < xs_len
                           then
                             (let uu____10488 =
                                FStar_Util.first_N args_len xs2  in
                              match uu____10488 with
                              | (xs3,xs_rest) ->
                                  let k3 =
                                    let uu____10518 =
                                      FStar_Syntax_Syntax.mk_GTotal k  in
                                    FStar_Syntax_Util.arrow xs_rest
                                      uu____10518
                                     in
                                  let uu____10521 =
                                    FStar_Syntax_Util.subst_of_list xs3 args
                                     in
                                  FStar_Syntax_Subst.subst uu____10521 k3)
                           else
                             (let uu____10524 =
                                let uu____10525 =
                                  FStar_Syntax_Print.term_to_string k  in
                                let uu____10526 =
                                  FStar_Syntax_Print.binders_to_string ", "
                                    xs2
                                   in
                                let uu____10527 =
                                  FStar_Syntax_Print.args_to_string args  in
                                FStar_Util.format3
                                  "k=%s\nxs=%s\nargs=%s\nIll-formed substitutution"
                                  uu____10525 uu____10526 uu____10527
                                 in
                              failwith uu____10524)
                          in
                       let uu____10528 =
                         let uu____10534 =
                           let uu____10542 =
                             FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Normalize.Beta] env k1
                              in
                           FStar_Syntax_Util.arrow_formals uu____10542  in
                         match uu____10534 with
                         | (bs,k1') ->
                             let uu____10560 =
                               let uu____10568 =
                                 FStar_TypeChecker_Normalize.normalize
                                   [FStar_TypeChecker_Normalize.Beta] env k2
                                  in
                               FStar_Syntax_Util.arrow_formals uu____10568
                                in
                             (match uu____10560 with
                              | (cs,k2') ->
                                  let k1'_xs = subst_k k1' bs args1  in
                                  let k2'_ys = subst_k k2' cs args2  in
                                  let sub_prob =
                                    let uu____10589 =
                                      mk_problem (p_scope orig) orig k1'_xs
                                        FStar_TypeChecker_Common.EQ k2'_ys
                                        None "flex-flex kinding"
                                       in
                                    FStar_All.pipe_left
                                      (fun _0_58  ->
                                         FStar_TypeChecker_Common.TProb _0_58)
                                      uu____10589
                                     in
                                  let uu____10594 =
                                    let uu____10597 =
                                      let uu____10598 =
                                        FStar_Syntax_Subst.compress k1'  in
                                      uu____10598.FStar_Syntax_Syntax.n  in
                                    let uu____10601 =
                                      let uu____10602 =
                                        FStar_Syntax_Subst.compress k2'  in
                                      uu____10602.FStar_Syntax_Syntax.n  in
                                    (uu____10597, uu____10601)  in
                                  (match uu____10594 with
                                   | (FStar_Syntax_Syntax.Tm_type
                                      uu____10610,uu____10611) ->
                                       (k1', [sub_prob])
                                   | (uu____10615,FStar_Syntax_Syntax.Tm_type
                                      uu____10616) -> (k2', [sub_prob])
                                   | uu____10620 ->
                                       let uu____10623 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____10623 with
                                        | (t,uu____10632) ->
                                            let uu____10633 = new_uvar r zs t
                                               in
                                            (match uu____10633 with
                                             | (k_zs,uu____10642) ->
                                                 let kprob =
                                                   let uu____10644 =
                                                     mk_problem
                                                       (p_scope orig) orig
                                                       k1'_xs
                                                       FStar_TypeChecker_Common.EQ
                                                       k_zs None
                                                       "flex-flex kinding"
                                                      in
                                                   FStar_All.pipe_left
                                                     (fun _0_59  ->
                                                        FStar_TypeChecker_Common.TProb
                                                          _0_59) uu____10644
                                                    in
                                                 (k_zs, [sub_prob; kprob])))))
                          in
                       match uu____10528 with
                       | (k_u',sub_probs) ->
                           let uu____10658 =
                             let uu____10666 =
                               let uu____10667 = new_uvar r zs k_u'  in
                               FStar_All.pipe_left FStar_Pervasives.fst
                                 uu____10667
                                in
                             let uu____10672 =
                               let uu____10675 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow xs1 uu____10675  in
                             let uu____10678 =
                               let uu____10681 =
                                 FStar_Syntax_Syntax.mk_Total k_u'  in
                               FStar_Syntax_Util.arrow ys1 uu____10681  in
                             (uu____10666, uu____10672, uu____10678)  in
                           (match uu____10658 with
                            | (u_zs,knew1,knew2) ->
                                let sub1 = u_abs knew1 xs1 u_zs  in
                                let uu____10700 =
                                  occurs_check env wl1 (u1, k1) sub1  in
                                (match uu____10700 with
                                 | (occurs_ok,msg) ->
                                     if Prims.op_Negation occurs_ok
                                     then
                                       giveup_or_defer1 orig
                                         "flex-flex: failed occcurs check"
                                     else
                                       (let sol1 = TERM ((u1, k1), sub1)  in
                                        let uu____10724 =
                                          FStar_Unionfind.equivalent u1 u2
                                           in
                                        if uu____10724
                                        then
                                          let wl2 =
                                            solve_prob orig None [sol1] wl1
                                             in
                                          solve env wl2
                                        else
                                          (let sub2 = u_abs knew2 ys1 u_zs
                                              in
                                           let uu____10731 =
                                             occurs_check env wl1 (u2, k2)
                                               sub2
                                              in
                                           match uu____10731 with
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
             let solve_one_pat uu____10783 uu____10784 =
               match (uu____10783, uu____10784) with
               | ((t1,u1,k1,xs),(t2,u2,k2,args2)) ->
                   ((let uu____10888 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")
                        in
                     if uu____10888
                     then
                       let uu____10889 = FStar_Syntax_Print.term_to_string t1
                          in
                       let uu____10890 = FStar_Syntax_Print.term_to_string t2
                          in
                       FStar_Util.print2
                         "Trying flex-flex one pattern (%s) with %s\n"
                         uu____10889 uu____10890
                     else ());
                    (let uu____10892 = FStar_Unionfind.equivalent u1 u2  in
                     if uu____10892
                     then
                       let sub_probs =
                         FStar_List.map2
                           (fun uu____10902  ->
                              fun uu____10903  ->
                                match (uu____10902, uu____10903) with
                                | ((a,uu____10913),(t21,uu____10915)) ->
                                    let uu____10920 =
                                      let uu____10923 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      mk_problem (p_scope orig) orig
                                        uu____10923
                                        FStar_TypeChecker_Common.EQ t21 None
                                        "flex-flex index"
                                       in
                                    FStar_All.pipe_right uu____10920
                                      (fun _0_60  ->
                                         FStar_TypeChecker_Common.TProb _0_60))
                           xs args2
                          in
                       let guard =
                         let uu____10927 =
                           FStar_List.map
                             (fun p  ->
                                FStar_All.pipe_right (p_guard p)
                                  FStar_Pervasives.fst) sub_probs
                            in
                         FStar_Syntax_Util.mk_conj_l uu____10927  in
                       let wl1 = solve_prob orig (Some guard) [] wl  in
                       solve env (attempt sub_probs wl1)
                     else
                       (let t21 = sn env t2  in
                        let rhs_vars = FStar_Syntax_Free.names t21  in
                        let uu____10937 = occurs_check env wl (u1, k1) t21
                           in
                        match uu____10937 with
                        | (occurs_ok,uu____10946) ->
                            let lhs_vars =
                              FStar_Syntax_Free.names_of_binders xs  in
                            let uu____10951 =
                              occurs_ok &&
                                (FStar_Util.set_is_subset_of rhs_vars
                                   lhs_vars)
                               in
                            if uu____10951
                            then
                              let sol =
                                let uu____10953 =
                                  let uu____10958 = u_abs k1 xs t21  in
                                  ((u1, k1), uu____10958)  in
                                TERM uu____10953  in
                              let wl1 = solve_prob orig None [sol] wl  in
                              solve env wl1
                            else
                              (let uu____10971 =
                                 occurs_ok &&
                                   (FStar_All.pipe_left Prims.op_Negation
                                      wl.defer_ok)
                                  in
                               if uu____10971
                               then
                                 let uu____10972 =
                                   force_quasi_pattern (Some xs)
                                     (t21, u2, k2, args2)
                                    in
                                 match uu____10972 with
                                 | (sol,(uu____10986,u21,k21,ys)) ->
                                     let wl1 =
                                       extend_solution (p_pid orig) [sol] wl
                                        in
                                     ((let uu____10996 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env)
                                           (FStar_Options.Other
                                              "QuasiPattern")
                                          in
                                       if uu____10996
                                       then
                                         let uu____10997 =
                                           uvi_to_string env sol  in
                                         FStar_Util.print1
                                           "flex-flex quasi pattern (2): %s\n"
                                           uu____10997
                                       else ());
                                      (match orig with
                                       | FStar_TypeChecker_Common.TProb p ->
                                           solve_t env p wl1
                                       | uu____11002 ->
                                           giveup env "impossible" orig))
                               else
                                 giveup_or_defer1 orig "flex-flex constraint"))))
                in
             let uu____11004 = lhs  in
             match uu____11004 with
             | (t1,u1,k1,args1) ->
                 let uu____11009 = rhs  in
                 (match uu____11009 with
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
                       | uu____11035 ->
                           if wl.defer_ok
                           then
                             giveup_or_defer1 orig
                               "flex-flex: neither side is a pattern"
                           else
                             (let uu____11041 =
                                force_quasi_pattern None (t1, u1, k1, args1)
                                 in
                              match uu____11041 with
                              | (sol,uu____11048) ->
                                  let wl1 =
                                    extend_solution (p_pid orig) [sol] wl  in
                                  ((let uu____11051 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        (FStar_Options.Other "QuasiPattern")
                                       in
                                    if uu____11051
                                    then
                                      let uu____11052 = uvi_to_string env sol
                                         in
                                      FStar_Util.print1
                                        "flex-flex quasi pattern (1): %s\n"
                                        uu____11052
                                    else ());
                                   (match orig with
                                    | FStar_TypeChecker_Common.TProb p ->
                                        solve_t env p wl1
                                    | uu____11057 ->
                                        giveup env "impossible" orig))))))
           in
        let orig = FStar_TypeChecker_Common.TProb problem  in
        let uu____11059 =
          FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
            problem.FStar_TypeChecker_Common.rhs
           in
        if uu____11059
        then
          let uu____11060 = solve_prob orig None [] wl  in
          solve env uu____11060
        else
          (let t1 = problem.FStar_TypeChecker_Common.lhs  in
           let t2 = problem.FStar_TypeChecker_Common.rhs  in
           let uu____11064 = FStar_Util.physical_equality t1 t2  in
           if uu____11064
           then
             let uu____11065 = solve_prob orig None [] wl  in
             solve env uu____11065
           else
             ((let uu____11068 =
                 FStar_TypeChecker_Env.debug env
                   (FStar_Options.Other "RelCheck")
                  in
               if uu____11068
               then
                 let uu____11069 =
                   FStar_Util.string_of_int
                     problem.FStar_TypeChecker_Common.pid
                    in
                 FStar_Util.print1 "Attempting %s\n" uu____11069
               else ());
              (let r = FStar_TypeChecker_Env.get_range env  in
               match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
               with
               | (FStar_Syntax_Syntax.Tm_bvar uu____11072,uu____11073) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (uu____11074,FStar_Syntax_Syntax.Tm_bvar uu____11075) ->
                   failwith
                     "Only locally nameless! We should never see a de Bruijn variable"
               | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                  u2) -> solve_one_universe_eq env orig u1 u2 wl
               | (FStar_Syntax_Syntax.Tm_arrow
                  (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                   let mk_c c uu___130_11115 =
                     match uu___130_11115 with
                     | [] -> c
                     | bs ->
                         let uu____11129 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs, c)) None
                             c.FStar_Syntax_Syntax.pos
                            in
                         FStar_Syntax_Syntax.mk_Total uu____11129
                      in
                   let uu____11139 =
                     match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                   (match uu____11139 with
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
                                   let uu____11225 =
                                     FStar_Options.use_eq_at_higher_order ()
                                      in
                                   if uu____11225
                                   then FStar_TypeChecker_Common.EQ
                                   else
                                     problem.FStar_TypeChecker_Common.relation
                                    in
                                 let uu____11227 =
                                   mk_problem scope orig c12 rel c22 None
                                     "function co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_61  ->
                                      FStar_TypeChecker_Common.CProb _0_61)
                                   uu____11227))
               | (FStar_Syntax_Syntax.Tm_abs
                  (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                  (bs2,tbody2,lopt2)) ->
                   let mk_t t l uu___131_11304 =
                     match uu___131_11304 with
                     | [] -> t
                     | bs ->
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_abs (bs, t, l)) None
                           t.FStar_Syntax_Syntax.pos
                      in
                   let uu____11339 =
                     match_num_binders (bs1, (mk_t tbody1 lopt1))
                       (bs2, (mk_t tbody2 lopt2))
                      in
                   (match uu____11339 with
                    | ((bs11,tbody11),(bs21,tbody21)) ->
                        solve_binders env bs11 bs21 orig wl
                          (fun scope  ->
                             fun env1  ->
                               fun subst1  ->
                                 let uu____11422 =
                                   let uu____11425 =
                                     FStar_Syntax_Subst.subst subst1 tbody11
                                      in
                                   let uu____11426 =
                                     FStar_Syntax_Subst.subst subst1 tbody21
                                      in
                                   mk_problem scope orig uu____11425
                                     problem.FStar_TypeChecker_Common.relation
                                     uu____11426 None "lambda co-domain"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_62  ->
                                      FStar_TypeChecker_Common.TProb _0_62)
                                   uu____11422))
               | (FStar_Syntax_Syntax.Tm_abs uu____11429,uu____11430) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11453 -> true
                     | uu____11468 -> false  in
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
                   let uu____11496 =
                     let uu____11507 = maybe_eta t1  in
                     let uu____11512 = maybe_eta t2  in
                     (uu____11507, uu____11512)  in
                   (match uu____11496 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11543 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11543.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11543.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11543.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11543.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11543.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11543.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11543.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11543.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11562 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11562
                        then
                          let uu____11563 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11563 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11584 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11584
                        then
                          let uu____11585 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11585 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11590 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (uu____11601,FStar_Syntax_Syntax.Tm_abs uu____11602) ->
                   let is_abs t =
                     match t.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_abs uu____11625 -> true
                     | uu____11640 -> false  in
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
                   let uu____11668 =
                     let uu____11679 = maybe_eta t1  in
                     let uu____11684 = maybe_eta t2  in
                     (uu____11679, uu____11684)  in
                   (match uu____11668 with
                    | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                        solve_t env
                          (let uu___164_11715 = problem  in
                           {
                             FStar_TypeChecker_Common.pid =
                               (uu___164_11715.FStar_TypeChecker_Common.pid);
                             FStar_TypeChecker_Common.lhs = t11;
                             FStar_TypeChecker_Common.relation =
                               (uu___164_11715.FStar_TypeChecker_Common.relation);
                             FStar_TypeChecker_Common.rhs = t21;
                             FStar_TypeChecker_Common.element =
                               (uu___164_11715.FStar_TypeChecker_Common.element);
                             FStar_TypeChecker_Common.logical_guard =
                               (uu___164_11715.FStar_TypeChecker_Common.logical_guard);
                             FStar_TypeChecker_Common.scope =
                               (uu___164_11715.FStar_TypeChecker_Common.scope);
                             FStar_TypeChecker_Common.reason =
                               (uu___164_11715.FStar_TypeChecker_Common.reason);
                             FStar_TypeChecker_Common.loc =
                               (uu___164_11715.FStar_TypeChecker_Common.loc);
                             FStar_TypeChecker_Common.rank =
                               (uu___164_11715.FStar_TypeChecker_Common.rank)
                           }) wl
                    | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                        let uu____11734 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11734
                        then
                          let uu____11735 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11735 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                        let uu____11756 =
                          (is_flex not_abs) &&
                            ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                           in
                        if uu____11756
                        then
                          let uu____11757 = destruct_flex_pattern env not_abs
                             in
                          solve_t_flex_rigid true orig uu____11757 t_abs wl
                        else
                          giveup env
                            "head tag mismatch: RHS is an abstraction" orig
                    | uu____11762 ->
                        failwith
                          "Impossible: at least one side is an abstraction")
               | (FStar_Syntax_Syntax.Tm_refine
                  uu____11773,FStar_Syntax_Syntax.Tm_refine uu____11774) ->
                   let uu____11783 = as_refinement env wl t1  in
                   (match uu____11783 with
                    | (x1,phi1) ->
                        let uu____11788 = as_refinement env wl t2  in
                        (match uu____11788 with
                         | (x2,phi2) ->
                             let base_prob =
                               let uu____11794 =
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
                                 uu____11794
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
                               let uu____11827 = imp phi12 phi22  in
                               FStar_All.pipe_right uu____11827
                                 (guard_on_element wl problem x11)
                                in
                             let fallback uu____11831 =
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
                                 let uu____11837 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____11837 impl
                                  in
                               let wl1 = solve_prob orig (Some guard) [] wl
                                  in
                               solve env1 (attempt [base_prob] wl1)  in
                             if
                               problem.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                             then
                               let ref_prob =
                                 let uu____11844 =
                                   let uu____11847 =
                                     let uu____11848 =
                                       FStar_Syntax_Syntax.mk_binder x11  in
                                     uu____11848 :: (p_scope orig)  in
                                   mk_problem uu____11847 orig phi11
                                     FStar_TypeChecker_Common.EQ phi21 None
                                     "refinement formula"
                                    in
                                 FStar_All.pipe_left
                                   (fun _0_64  ->
                                      FStar_TypeChecker_Common.TProb _0_64)
                                   uu____11844
                                  in
                               let uu____11851 =
                                 solve env1
                                   (let uu___165_11852 = wl  in
                                    {
                                      attempting = [ref_prob];
                                      wl_deferred = [];
                                      ctr = (uu___165_11852.ctr);
                                      defer_ok = false;
                                      smt_ok = (uu___165_11852.smt_ok);
                                      tcenv = (uu___165_11852.tcenv)
                                    })
                                  in
                               (match uu____11851 with
                                | Failed uu____11856 -> fallback ()
                                | Success uu____11859 ->
                                    let guard =
                                      let uu____11863 =
                                        FStar_All.pipe_right
                                          (p_guard base_prob)
                                          FStar_Pervasives.fst
                                         in
                                      let uu____11866 =
                                        let uu____11867 =
                                          FStar_All.pipe_right
                                            (p_guard ref_prob)
                                            FStar_Pervasives.fst
                                           in
                                        FStar_All.pipe_right uu____11867
                                          (guard_on_element wl problem x11)
                                         in
                                      FStar_Syntax_Util.mk_conj uu____11863
                                        uu____11866
                                       in
                                    let wl1 =
                                      solve_prob orig (Some guard) [] wl  in
                                    let wl2 =
                                      let uu___166_11874 = wl1  in
                                      {
                                        attempting =
                                          (uu___166_11874.attempting);
                                        wl_deferred =
                                          (uu___166_11874.wl_deferred);
                                        ctr =
                                          (wl1.ctr + (Prims.parse_int "1"));
                                        defer_ok = (uu___166_11874.defer_ok);
                                        smt_ok = (uu___166_11874.smt_ok);
                                        tcenv = (uu___166_11874.tcenv)
                                      }  in
                                    solve env1 (attempt [base_prob] wl2))
                             else fallback ()))
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11876,FStar_Syntax_Syntax.Tm_uvar uu____11877) ->
                   let uu____11894 = destruct_flex_t t1  in
                   let uu____11895 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11894 uu____11895
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11896;
                     FStar_Syntax_Syntax.tk = uu____11897;
                     FStar_Syntax_Syntax.pos = uu____11898;
                     FStar_Syntax_Syntax.vars = uu____11899;_},uu____11900),FStar_Syntax_Syntax.Tm_uvar
                  uu____11901) ->
                   let uu____11932 = destruct_flex_t t1  in
                   let uu____11933 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11932 uu____11933
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____11934,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11935;
                     FStar_Syntax_Syntax.tk = uu____11936;
                     FStar_Syntax_Syntax.pos = uu____11937;
                     FStar_Syntax_Syntax.vars = uu____11938;_},uu____11939))
                   ->
                   let uu____11970 = destruct_flex_t t1  in
                   let uu____11971 = destruct_flex_t t2  in
                   flex_flex1 orig uu____11970 uu____11971
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11972;
                     FStar_Syntax_Syntax.tk = uu____11973;
                     FStar_Syntax_Syntax.pos = uu____11974;
                     FStar_Syntax_Syntax.vars = uu____11975;_},uu____11976),FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____11977;
                     FStar_Syntax_Syntax.tk = uu____11978;
                     FStar_Syntax_Syntax.pos = uu____11979;
                     FStar_Syntax_Syntax.vars = uu____11980;_},uu____11981))
                   ->
                   let uu____12026 = destruct_flex_t t1  in
                   let uu____12027 = destruct_flex_t t2  in
                   flex_flex1 orig uu____12026 uu____12027
               | (FStar_Syntax_Syntax.Tm_uvar uu____12028,uu____12029) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12038 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12038 t2 wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12042;
                     FStar_Syntax_Syntax.tk = uu____12043;
                     FStar_Syntax_Syntax.pos = uu____12044;
                     FStar_Syntax_Syntax.vars = uu____12045;_},uu____12046),uu____12047)
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   ->
                   let uu____12070 = destruct_flex_pattern env t1  in
                   solve_t_flex_rigid false orig uu____12070 t2 wl
               | (uu____12074,FStar_Syntax_Syntax.Tm_uvar uu____12075) when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (uu____12084,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12085;
                     FStar_Syntax_Syntax.tk = uu____12086;
                     FStar_Syntax_Syntax.pos = uu____12087;
                     FStar_Syntax_Syntax.vars = uu____12088;_},uu____12089))
                   when
                   problem.FStar_TypeChecker_Common.relation =
                     FStar_TypeChecker_Common.EQ
                   -> solve_t env (invert problem) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12112,FStar_Syntax_Syntax.Tm_type uu____12113) ->
                   solve_t' env
                     (let uu___167_12122 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12122.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12122.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12122.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12122.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12122.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12122.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12122.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12122.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12122.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12123;
                     FStar_Syntax_Syntax.tk = uu____12124;
                     FStar_Syntax_Syntax.pos = uu____12125;
                     FStar_Syntax_Syntax.vars = uu____12126;_},uu____12127),FStar_Syntax_Syntax.Tm_type
                  uu____12128) ->
                   solve_t' env
                     (let uu___167_12151 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12151.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12151.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12151.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12151.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12151.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12151.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12151.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12151.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12151.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar
                  uu____12152,FStar_Syntax_Syntax.Tm_arrow uu____12153) ->
                   solve_t' env
                     (let uu___167_12169 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12169.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12169.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12169.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12169.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12169.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12169.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12169.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12169.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12169.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12170;
                     FStar_Syntax_Syntax.tk = uu____12171;
                     FStar_Syntax_Syntax.pos = uu____12172;
                     FStar_Syntax_Syntax.vars = uu____12173;_},uu____12174),FStar_Syntax_Syntax.Tm_arrow
                  uu____12175) ->
                   solve_t' env
                     (let uu___167_12205 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___167_12205.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___167_12205.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ;
                        FStar_TypeChecker_Common.rhs =
                          (uu___167_12205.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___167_12205.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___167_12205.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___167_12205.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___167_12205.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___167_12205.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___167_12205.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_uvar uu____12206,uu____12207) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12218 =
                        let uu____12219 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12219  in
                      if uu____12218
                      then
                        let uu____12220 =
                          FStar_All.pipe_left
                            (fun _0_65  ->
                               FStar_TypeChecker_Common.TProb _0_65)
                            (let uu___168_12223 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12223.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12223.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12223.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12223.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12223.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12223.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12223.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12223.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12223.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12224 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12220 uu____12224 t2
                          wl
                      else
                        (let uu____12229 = base_and_refinement env wl t2  in
                         match uu____12229 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12259 =
                                    FStar_All.pipe_left
                                      (fun _0_66  ->
                                         FStar_TypeChecker_Common.TProb _0_66)
                                      (let uu___169_12262 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12262.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12262.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12262.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12262.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12262.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12262.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12262.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12262.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12262.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12263 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12259
                                    uu____12263 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12278 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12278.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12278.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12281 =
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
                                      uu____12281
                                     in
                                  let guard =
                                    let uu____12289 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12289
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12295;
                     FStar_Syntax_Syntax.tk = uu____12296;
                     FStar_Syntax_Syntax.pos = uu____12297;
                     FStar_Syntax_Syntax.vars = uu____12298;_},uu____12299),uu____12300)
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "flex-rigid subtyping deferred" orig wl)
                   else
                     (let new_rel = problem.FStar_TypeChecker_Common.relation
                         in
                      let uu____12325 =
                        let uu____12326 = is_top_level_prob orig  in
                        FStar_All.pipe_left Prims.op_Negation uu____12326  in
                      if uu____12325
                      then
                        let uu____12327 =
                          FStar_All.pipe_left
                            (fun _0_68  ->
                               FStar_TypeChecker_Common.TProb _0_68)
                            (let uu___168_12330 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___168_12330.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___168_12330.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation = new_rel;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___168_12330.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___168_12330.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___168_12330.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___168_12330.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___168_12330.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___168_12330.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___168_12330.FStar_TypeChecker_Common.rank)
                             })
                           in
                        let uu____12331 = destruct_flex_pattern env t1  in
                        solve_t_flex_rigid false uu____12327 uu____12331 t2
                          wl
                      else
                        (let uu____12336 = base_and_refinement env wl t2  in
                         match uu____12336 with
                         | (t_base,ref_opt) ->
                             (match ref_opt with
                              | None  ->
                                  let uu____12366 =
                                    FStar_All.pipe_left
                                      (fun _0_69  ->
                                         FStar_TypeChecker_Common.TProb _0_69)
                                      (let uu___169_12369 = problem  in
                                       {
                                         FStar_TypeChecker_Common.pid =
                                           (uu___169_12369.FStar_TypeChecker_Common.pid);
                                         FStar_TypeChecker_Common.lhs =
                                           (uu___169_12369.FStar_TypeChecker_Common.lhs);
                                         FStar_TypeChecker_Common.relation =
                                           new_rel;
                                         FStar_TypeChecker_Common.rhs =
                                           (uu___169_12369.FStar_TypeChecker_Common.rhs);
                                         FStar_TypeChecker_Common.element =
                                           (uu___169_12369.FStar_TypeChecker_Common.element);
                                         FStar_TypeChecker_Common.logical_guard
                                           =
                                           (uu___169_12369.FStar_TypeChecker_Common.logical_guard);
                                         FStar_TypeChecker_Common.scope =
                                           (uu___169_12369.FStar_TypeChecker_Common.scope);
                                         FStar_TypeChecker_Common.reason =
                                           (uu___169_12369.FStar_TypeChecker_Common.reason);
                                         FStar_TypeChecker_Common.loc =
                                           (uu___169_12369.FStar_TypeChecker_Common.loc);
                                         FStar_TypeChecker_Common.rank =
                                           (uu___169_12369.FStar_TypeChecker_Common.rank)
                                       })
                                     in
                                  let uu____12370 =
                                    destruct_flex_pattern env t1  in
                                  solve_t_flex_rigid false uu____12366
                                    uu____12370 t_base wl
                              | Some (y,phi) ->
                                  let y' =
                                    let uu___170_12385 = y  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___170_12385.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___170_12385.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = t1
                                    }  in
                                  let impl =
                                    guard_on_element wl problem y' phi  in
                                  let base_prob =
                                    let uu____12388 =
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
                                      uu____12388
                                     in
                                  let guard =
                                    let uu____12396 =
                                      FStar_All.pipe_right
                                        (p_guard base_prob)
                                        FStar_Pervasives.fst
                                       in
                                    FStar_Syntax_Util.mk_conj uu____12396
                                      impl
                                     in
                                  let wl1 =
                                    solve_prob orig (Some guard) [] wl  in
                                  solve env (attempt [base_prob] wl1))))
               | (uu____12402,FStar_Syntax_Syntax.Tm_uvar uu____12403) ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12413 = base_and_refinement env wl t1  in
                      match uu____12413 with
                      | (t_base,uu____12424) ->
                          solve_t env
                            (let uu___171_12439 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12439.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12439.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12439.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12439.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12439.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12439.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12439.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12439.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (uu____12442,FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                       uu____12443;
                     FStar_Syntax_Syntax.tk = uu____12444;
                     FStar_Syntax_Syntax.pos = uu____12445;
                     FStar_Syntax_Syntax.vars = uu____12446;_},uu____12447))
                   ->
                   if wl.defer_ok
                   then
                     solve env
                       (defer "rigid-flex subtyping deferred" orig wl)
                   else
                     (let uu____12471 = base_and_refinement env wl t1  in
                      match uu____12471 with
                      | (t_base,uu____12482) ->
                          solve_t env
                            (let uu___171_12497 = problem  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___171_12497.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs = t_base;
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___171_12497.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___171_12497.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___171_12497.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.scope =
                                 (uu___171_12497.FStar_TypeChecker_Common.scope);
                               FStar_TypeChecker_Common.reason =
                                 (uu___171_12497.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___171_12497.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___171_12497.FStar_TypeChecker_Common.rank)
                             }) wl)
               | (FStar_Syntax_Syntax.Tm_refine uu____12500,uu____12501) ->
                   let t21 =
                     let uu____12509 = base_and_refinement env wl t2  in
                     FStar_All.pipe_left force_refinement uu____12509  in
                   solve_t env
                     (let uu___172_12522 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___172_12522.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___172_12522.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___172_12522.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___172_12522.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___172_12522.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___172_12522.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___172_12522.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___172_12522.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___172_12522.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____12523,FStar_Syntax_Syntax.Tm_refine uu____12524) ->
                   let t11 =
                     let uu____12532 = base_and_refinement env wl t1  in
                     FStar_All.pipe_left force_refinement uu____12532  in
                   solve_t env
                     (let uu___173_12545 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___173_12545.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___173_12545.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___173_12545.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___173_12545.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___173_12545.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___173_12545.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___173_12545.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___173_12545.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___173_12545.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_match uu____12548,uu____12549) ->
                   let head1 =
                     let uu____12568 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12568 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12599 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12599 FStar_Pervasives.fst
                      in
                   let uu____12627 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12627
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12636 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12636
                      then
                        let guard =
                          let uu____12643 =
                            let uu____12644 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12644 = FStar_Syntax_Util.Equal  in
                          if uu____12643
                          then None
                          else
                            (let uu____12647 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_71  -> Some _0_71)
                               uu____12647)
                           in
                        let uu____12649 = solve_prob orig guard [] wl  in
                        solve env uu____12649
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_uinst uu____12652,uu____12653) ->
                   let head1 =
                     let uu____12661 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12661 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12692 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12692 FStar_Pervasives.fst
                      in
                   let uu____12720 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12720
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12729 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12729
                      then
                        let guard =
                          let uu____12736 =
                            let uu____12737 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12737 = FStar_Syntax_Util.Equal  in
                          if uu____12736
                          then None
                          else
                            (let uu____12740 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_72  -> Some _0_72)
                               uu____12740)
                           in
                        let uu____12742 = solve_prob orig guard [] wl  in
                        solve env uu____12742
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_name uu____12745,uu____12746) ->
                   let head1 =
                     let uu____12750 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12750 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12781 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12781 FStar_Pervasives.fst
                      in
                   let uu____12809 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12809
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12818 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12818
                      then
                        let guard =
                          let uu____12825 =
                            let uu____12826 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12826 = FStar_Syntax_Util.Equal  in
                          if uu____12825
                          then None
                          else
                            (let uu____12829 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_73  -> Some _0_73)
                               uu____12829)
                           in
                        let uu____12831 = solve_prob orig guard [] wl  in
                        solve env uu____12831
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_constant uu____12834,uu____12835) ->
                   let head1 =
                     let uu____12839 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12839 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12870 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12870 FStar_Pervasives.fst
                      in
                   let uu____12898 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12898
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12907 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12907
                      then
                        let guard =
                          let uu____12914 =
                            let uu____12915 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____12915 = FStar_Syntax_Util.Equal  in
                          if uu____12914
                          then None
                          else
                            (let uu____12918 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_74  -> Some _0_74)
                               uu____12918)
                           in
                        let uu____12920 = solve_prob orig guard [] wl  in
                        solve env uu____12920
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_fvar uu____12923,uu____12924) ->
                   let head1 =
                     let uu____12928 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____12928 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____12959 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____12959 FStar_Pervasives.fst
                      in
                   let uu____12987 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____12987
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____12996 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____12996
                      then
                        let guard =
                          let uu____13003 =
                            let uu____13004 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13004 = FStar_Syntax_Util.Equal  in
                          if uu____13003
                          then None
                          else
                            (let uu____13007 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_75  -> Some _0_75)
                               uu____13007)
                           in
                        let uu____13009 = solve_prob orig guard [] wl  in
                        solve env uu____13009
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_app uu____13012,uu____13013) ->
                   let head1 =
                     let uu____13026 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13026 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13057 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13057 FStar_Pervasives.fst
                      in
                   let uu____13085 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13085
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13094 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13094
                      then
                        let guard =
                          let uu____13101 =
                            let uu____13102 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13102 = FStar_Syntax_Util.Equal  in
                          if uu____13101
                          then None
                          else
                            (let uu____13105 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_76  -> Some _0_76)
                               uu____13105)
                           in
                        let uu____13107 = solve_prob orig guard [] wl  in
                        solve env uu____13107
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13110,FStar_Syntax_Syntax.Tm_match uu____13111) ->
                   let head1 =
                     let uu____13130 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13130 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13161 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13161 FStar_Pervasives.fst
                      in
                   let uu____13189 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13189
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13198 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13198
                      then
                        let guard =
                          let uu____13205 =
                            let uu____13206 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13206 = FStar_Syntax_Util.Equal  in
                          if uu____13205
                          then None
                          else
                            (let uu____13209 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_77  -> Some _0_77)
                               uu____13209)
                           in
                        let uu____13211 = solve_prob orig guard [] wl  in
                        solve env uu____13211
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13214,FStar_Syntax_Syntax.Tm_uinst uu____13215) ->
                   let head1 =
                     let uu____13223 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13223 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13254 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13254 FStar_Pervasives.fst
                      in
                   let uu____13282 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13282
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13291 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13291
                      then
                        let guard =
                          let uu____13298 =
                            let uu____13299 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13299 = FStar_Syntax_Util.Equal  in
                          if uu____13298
                          then None
                          else
                            (let uu____13302 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_78  -> Some _0_78)
                               uu____13302)
                           in
                        let uu____13304 = solve_prob orig guard [] wl  in
                        solve env uu____13304
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13307,FStar_Syntax_Syntax.Tm_name uu____13308) ->
                   let head1 =
                     let uu____13312 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13312 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13343 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13343 FStar_Pervasives.fst
                      in
                   let uu____13371 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13371
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13380 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13380
                      then
                        let guard =
                          let uu____13387 =
                            let uu____13388 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13388 = FStar_Syntax_Util.Equal  in
                          if uu____13387
                          then None
                          else
                            (let uu____13391 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_79  -> Some _0_79)
                               uu____13391)
                           in
                        let uu____13393 = solve_prob orig guard [] wl  in
                        solve env uu____13393
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13396,FStar_Syntax_Syntax.Tm_constant uu____13397) ->
                   let head1 =
                     let uu____13401 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13401 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13432 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13432 FStar_Pervasives.fst
                      in
                   let uu____13460 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13460
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13469 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13469
                      then
                        let guard =
                          let uu____13476 =
                            let uu____13477 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13477 = FStar_Syntax_Util.Equal  in
                          if uu____13476
                          then None
                          else
                            (let uu____13480 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_80  -> Some _0_80)
                               uu____13480)
                           in
                        let uu____13482 = solve_prob orig guard [] wl  in
                        solve env uu____13482
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13485,FStar_Syntax_Syntax.Tm_fvar uu____13486) ->
                   let head1 =
                     let uu____13490 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13490 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13521 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13521 FStar_Pervasives.fst
                      in
                   let uu____13549 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13549
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13558 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13558
                      then
                        let guard =
                          let uu____13565 =
                            let uu____13566 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13566 = FStar_Syntax_Util.Equal  in
                          if uu____13565
                          then None
                          else
                            (let uu____13569 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_81  -> Some _0_81)
                               uu____13569)
                           in
                        let uu____13571 = solve_prob orig guard [] wl  in
                        solve env uu____13571
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (uu____13574,FStar_Syntax_Syntax.Tm_app uu____13575) ->
                   let head1 =
                     let uu____13588 = FStar_Syntax_Util.head_and_args t1  in
                     FStar_All.pipe_right uu____13588 FStar_Pervasives.fst
                      in
                   let head2 =
                     let uu____13619 = FStar_Syntax_Util.head_and_args t2  in
                     FStar_All.pipe_right uu____13619 FStar_Pervasives.fst
                      in
                   let uu____13647 =
                     (((FStar_TypeChecker_Env.is_interpreted env head1) ||
                         (FStar_TypeChecker_Env.is_interpreted env head2))
                        && wl.smt_ok)
                       &&
                       (problem.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ)
                      in
                   if uu____13647
                   then
                     let uv1 = FStar_Syntax_Free.uvars t1  in
                     let uv2 = FStar_Syntax_Free.uvars t2  in
                     let uu____13656 =
                       (FStar_Util.set_is_empty uv1) &&
                         (FStar_Util.set_is_empty uv2)
                        in
                     (if uu____13656
                      then
                        let guard =
                          let uu____13663 =
                            let uu____13664 = FStar_Syntax_Util.eq_tm t1 t2
                               in
                            uu____13664 = FStar_Syntax_Util.Equal  in
                          if uu____13663
                          then None
                          else
                            (let uu____13667 = mk_eq2 env t1 t2  in
                             FStar_All.pipe_left (fun _0_82  -> Some _0_82)
                               uu____13667)
                           in
                        let uu____13669 = solve_prob orig guard [] wl  in
                        solve env uu____13669
                      else rigid_rigid_delta env orig wl head1 head2 t1 t2)
                   else rigid_rigid_delta env orig wl head1 head2 t1 t2
               | (FStar_Syntax_Syntax.Tm_ascribed
                  (t11,uu____13673,uu____13674),uu____13675) ->
                   solve_t' env
                     (let uu___174_13704 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___174_13704.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs = t11;
                        FStar_TypeChecker_Common.relation =
                          (uu___174_13704.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs =
                          (uu___174_13704.FStar_TypeChecker_Common.rhs);
                        FStar_TypeChecker_Common.element =
                          (uu___174_13704.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___174_13704.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___174_13704.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___174_13704.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___174_13704.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___174_13704.FStar_TypeChecker_Common.rank)
                      }) wl
               | (uu____13707,FStar_Syntax_Syntax.Tm_ascribed
                  (t21,uu____13709,uu____13710)) ->
                   solve_t' env
                     (let uu___175_13739 = problem  in
                      {
                        FStar_TypeChecker_Common.pid =
                          (uu___175_13739.FStar_TypeChecker_Common.pid);
                        FStar_TypeChecker_Common.lhs =
                          (uu___175_13739.FStar_TypeChecker_Common.lhs);
                        FStar_TypeChecker_Common.relation =
                          (uu___175_13739.FStar_TypeChecker_Common.relation);
                        FStar_TypeChecker_Common.rhs = t21;
                        FStar_TypeChecker_Common.element =
                          (uu___175_13739.FStar_TypeChecker_Common.element);
                        FStar_TypeChecker_Common.logical_guard =
                          (uu___175_13739.FStar_TypeChecker_Common.logical_guard);
                        FStar_TypeChecker_Common.scope =
                          (uu___175_13739.FStar_TypeChecker_Common.scope);
                        FStar_TypeChecker_Common.reason =
                          (uu___175_13739.FStar_TypeChecker_Common.reason);
                        FStar_TypeChecker_Common.loc =
                          (uu___175_13739.FStar_TypeChecker_Common.loc);
                        FStar_TypeChecker_Common.rank =
                          (uu___175_13739.FStar_TypeChecker_Common.rank)
                      }) wl
               | (FStar_Syntax_Syntax.Tm_let uu____13740,uu____13741) ->
                   let uu____13749 =
                     let uu____13750 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13751 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13750
                       uu____13751
                      in
                   failwith uu____13749
               | (FStar_Syntax_Syntax.Tm_meta uu____13752,uu____13753) ->
                   let uu____13758 =
                     let uu____13759 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13760 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13759
                       uu____13760
                      in
                   failwith uu____13758
               | (FStar_Syntax_Syntax.Tm_delayed uu____13761,uu____13762) ->
                   let uu____13783 =
                     let uu____13784 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13785 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13784
                       uu____13785
                      in
                   failwith uu____13783
               | (uu____13786,FStar_Syntax_Syntax.Tm_meta uu____13787) ->
                   let uu____13792 =
                     let uu____13793 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13794 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13793
                       uu____13794
                      in
                   failwith uu____13792
               | (uu____13795,FStar_Syntax_Syntax.Tm_delayed uu____13796) ->
                   let uu____13817 =
                     let uu____13818 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13819 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13818
                       uu____13819
                      in
                   failwith uu____13817
               | (uu____13820,FStar_Syntax_Syntax.Tm_let uu____13821) ->
                   let uu____13829 =
                     let uu____13830 = FStar_Syntax_Print.tag_of_term t1  in
                     let uu____13831 = FStar_Syntax_Print.tag_of_term t2  in
                     FStar_Util.format2 "Impossible: %s and %s" uu____13830
                       uu____13831
                      in
                   failwith uu____13829
               | uu____13832 -> giveup env "head tag mismatch" orig)))

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
          (let uu____13864 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____13864
           then
             FStar_Util.print_string
               "solve_c is using an equality constraint\n"
           else ());
          (let sub_probs =
             FStar_List.map2
               (fun uu____13872  ->
                  fun uu____13873  ->
                    match (uu____13872, uu____13873) with
                    | ((a1,uu____13883),(a2,uu____13885)) ->
                        let uu____13890 =
                          sub_prob a1 FStar_TypeChecker_Common.EQ a2
                            "effect arg"
                           in
                        FStar_All.pipe_left
                          (fun _0_83  -> FStar_TypeChecker_Common.TProb _0_83)
                          uu____13890)
               c1_comp.FStar_Syntax_Syntax.effect_args
               c2_comp.FStar_Syntax_Syntax.effect_args
              in
           let guard =
             let uu____13896 =
               FStar_List.map
                 (fun p  ->
                    FStar_All.pipe_right (p_guard p) FStar_Pervasives.fst)
                 sub_probs
                in
             FStar_Syntax_Util.mk_conj_l uu____13896  in
           let wl1 = solve_prob orig (Some guard) [] wl  in
           solve env (attempt sub_probs wl1))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____13916 =
            let wp =
              match c11.FStar_Syntax_Syntax.effect_args with
              | (wp1,uu____13923)::[] -> wp1
              | uu____13936 ->
                  let uu____13942 =
                    let uu____13943 =
                      FStar_Range.string_of_range
                        (FStar_Ident.range_of_lid
                           c11.FStar_Syntax_Syntax.effect_name)
                       in
                    FStar_Util.format1
                      "Unexpected number of indices on a normalized effect (%s)"
                      uu____13943
                     in
                  failwith uu____13942
               in
            let uu____13946 =
              let uu____13952 =
                let uu____13953 =
                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    c11.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____13953  in
              [uu____13952]  in
            {
              FStar_Syntax_Syntax.comp_univs =
                (c11.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (c21.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ =
                (c11.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____13946;
              FStar_Syntax_Syntax.flags = (c11.FStar_Syntax_Syntax.flags)
            }  in
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then let uu____13954 = lift_c1 ()  in solve_eq uu____13954 c21
          else
            (let is_null_wp_2 =
               FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                 (FStar_Util.for_some
                    (fun uu___132_13958  ->
                       match uu___132_13958 with
                       | FStar_Syntax_Syntax.TOTAL  -> true
                       | FStar_Syntax_Syntax.MLEFFECT  -> true
                       | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                       | uu____13959 -> false))
                in
             let uu____13960 =
               match ((c11.FStar_Syntax_Syntax.effect_args),
                       (c21.FStar_Syntax_Syntax.effect_args))
               with
               | ((wp1,uu____13984)::uu____13985,(wp2,uu____13987)::uu____13988)
                   -> (wp1, wp2)
               | uu____14029 ->
                   let uu____14042 =
                     let uu____14043 =
                       let uu____14046 =
                         let uu____14047 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____14048 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____14047 uu____14048
                          in
                       (uu____14046, (env.FStar_TypeChecker_Env.range))  in
                     FStar_Errors.Error uu____14043  in
                   raise uu____14042
                in
             match uu____13960 with
             | (wpc1,wpc2) ->
                 let uu____14065 = FStar_Util.physical_equality wpc1 wpc2  in
                 if uu____14065
                 then
                   let uu____14068 =
                     problem_using_guard orig
                       c11.FStar_Syntax_Syntax.result_typ
                       problem.FStar_TypeChecker_Common.relation
                       c21.FStar_Syntax_Syntax.result_typ None "result type"
                      in
                   solve_t env uu____14068 wl
                 else
                   (let uu____14072 =
                      let uu____14076 =
                        FStar_TypeChecker_Env.effect_decl_opt env
                          c21.FStar_Syntax_Syntax.effect_name
                         in
                      FStar_Util.must uu____14076  in
                    match uu____14072 with
                    | (c2_decl,qualifiers) ->
                        let uu____14088 =
                          FStar_All.pipe_right qualifiers
                            (FStar_List.contains
                               FStar_Syntax_Syntax.Reifiable)
                           in
                        if uu____14088
                        then
                          let c1_repr =
                            let uu____14091 =
                              let uu____14092 =
                                let uu____14093 = lift_c1 ()  in
                                FStar_Syntax_Syntax.mk_Comp uu____14093  in
                              let uu____14094 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c11.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14092 uu____14094
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14091
                             in
                          let c2_repr =
                            let uu____14096 =
                              let uu____14097 =
                                FStar_Syntax_Syntax.mk_Comp c21  in
                              let uu____14098 =
                                env.FStar_TypeChecker_Env.universe_of env
                                  c21.FStar_Syntax_Syntax.result_typ
                                 in
                              FStar_TypeChecker_Env.reify_comp env
                                uu____14097 uu____14098
                               in
                            FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Normalize.UnfoldUntil
                                 FStar_Syntax_Syntax.Delta_constant;
                              FStar_TypeChecker_Normalize.WHNF] env
                              uu____14096
                             in
                          let prob =
                            let uu____14100 =
                              let uu____14103 =
                                let uu____14104 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____14105 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____14104
                                  uu____14105
                                 in
                              sub_prob c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____14103
                               in
                            FStar_TypeChecker_Common.TProb uu____14100  in
                          let wl1 =
                            let uu____14107 =
                              let uu____14109 =
                                FStar_All.pipe_right (p_guard prob)
                                  FStar_Pervasives.fst
                                 in
                              Some uu____14109  in
                            solve_prob orig uu____14107 [] wl  in
                          solve env (attempt [prob] wl1)
                        else
                          (let g =
                             if env.FStar_TypeChecker_Env.lax
                             then FStar_Syntax_Util.t_true
                             else
                               if is_null_wp_2
                               then
                                 ((let uu____14116 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____14116
                                   then
                                     FStar_Util.print_string
                                       "Using trivial wp ... \n"
                                   else ());
                                  (let uu____14118 =
                                     let uu____14121 =
                                       let uu____14122 =
                                         let uu____14132 =
                                           let uu____14133 =
                                             let uu____14134 =
                                               env.FStar_TypeChecker_Env.universe_of
                                                 env
                                                 c11.FStar_Syntax_Syntax.result_typ
                                                in
                                             [uu____14134]  in
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             uu____14133 env c2_decl
                                             c2_decl.FStar_Syntax_Syntax.trivial
                                            in
                                         let uu____14135 =
                                           let uu____14137 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           let uu____14138 =
                                             let uu____14140 =
                                               let uu____14141 =
                                                 (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                   c11.FStar_Syntax_Syntax.result_typ
                                                   wpc1
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____14141
                                                in
                                             [uu____14140]  in
                                           uu____14137 :: uu____14138  in
                                         (uu____14132, uu____14135)  in
                                       FStar_Syntax_Syntax.Tm_app uu____14122
                                        in
                                     FStar_Syntax_Syntax.mk uu____14121  in
                                   uu____14118
                                     (Some
                                        (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                     r))
                               else
                                 (let uu____14152 =
                                    let uu____14155 =
                                      let uu____14156 =
                                        let uu____14166 =
                                          let uu____14167 =
                                            let uu____14168 =
                                              env.FStar_TypeChecker_Env.universe_of
                                                env
                                                c21.FStar_Syntax_Syntax.result_typ
                                               in
                                            [uu____14168]  in
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            uu____14167 env c2_decl
                                            c2_decl.FStar_Syntax_Syntax.stronger
                                           in
                                        let uu____14169 =
                                          let uu____14171 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____14172 =
                                            let uu____14174 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            let uu____14175 =
                                              let uu____14177 =
                                                let uu____14178 =
                                                  (edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                                                    c11.FStar_Syntax_Syntax.result_typ
                                                    wpc1
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_Syntax_Syntax.as_arg
                                                  uu____14178
                                                 in
                                              [uu____14177]  in
                                            uu____14174 :: uu____14175  in
                                          uu____14171 :: uu____14172  in
                                        (uu____14166, uu____14169)  in
                                      FStar_Syntax_Syntax.Tm_app uu____14156
                                       in
                                    FStar_Syntax_Syntax.mk uu____14155  in
                                  uu____14152
                                    (Some
                                       (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n))
                                    r)
                              in
                           let base_prob =
                             let uu____14189 =
                               sub_prob c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             FStar_All.pipe_left
                               (fun _0_84  ->
                                  FStar_TypeChecker_Common.TProb _0_84)
                               uu____14189
                              in
                           let wl1 =
                             let uu____14195 =
                               let uu____14197 =
                                 let uu____14200 =
                                   FStar_All.pipe_right (p_guard base_prob)
                                     FStar_Pervasives.fst
                                    in
                                 FStar_Syntax_Util.mk_conj uu____14200 g  in
                               FStar_All.pipe_left (fun _0_85  -> Some _0_85)
                                 uu____14197
                                in
                             solve_prob orig uu____14195 [] wl  in
                           solve env (attempt [base_prob] wl1))))
           in
        let uu____14210 = FStar_Util.physical_equality c1 c2  in
        if uu____14210
        then
          let uu____14211 = solve_prob orig None [] wl  in
          solve env uu____14211
        else
          ((let uu____14214 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____14214
            then
              let uu____14215 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____14216 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____14215
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____14216
            else ());
           (let uu____14218 =
              let uu____14221 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____14222 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____14221, uu____14222)  in
            match uu____14218 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14226),FStar_Syntax_Syntax.Total
                    (t2,uu____14228)) when
                     FStar_Syntax_Util.non_informative t2 ->
                     let uu____14241 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14241 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14244,FStar_Syntax_Syntax.Total uu____14245) ->
                     giveup env "incompatible monad ordering: GTot </: Tot"
                       orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14257),FStar_Syntax_Syntax.Total
                    (t2,uu____14259)) ->
                     let uu____14272 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14272 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____14276),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14278)) ->
                     let uu____14291 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14291 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____14295),FStar_Syntax_Syntax.GTotal
                    (t2,uu____14297)) ->
                     let uu____14310 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2 None
                         "result type"
                        in
                     solve_t env uu____14310 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____14313,FStar_Syntax_Syntax.Comp uu____14314) ->
                     let uu____14320 =
                       let uu___176_14323 = problem  in
                       let uu____14326 =
                         let uu____14327 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14327
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14323.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14326;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14323.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14323.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14323.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14323.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14323.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14323.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14323.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14323.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14320 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____14328,FStar_Syntax_Syntax.Comp uu____14329) ->
                     let uu____14335 =
                       let uu___176_14338 = problem  in
                       let uu____14341 =
                         let uu____14342 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14342
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___176_14338.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____14341;
                         FStar_TypeChecker_Common.relation =
                           (uu___176_14338.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___176_14338.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___176_14338.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___176_14338.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___176_14338.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___176_14338.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___176_14338.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___176_14338.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14335 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14343,FStar_Syntax_Syntax.GTotal uu____14344) ->
                     let uu____14350 =
                       let uu___177_14353 = problem  in
                       let uu____14356 =
                         let uu____14357 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14357
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14353.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14353.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14353.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14356;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14353.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14353.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14353.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14353.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14353.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14353.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14350 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14358,FStar_Syntax_Syntax.Total uu____14359) ->
                     let uu____14365 =
                       let uu___177_14368 = problem  in
                       let uu____14371 =
                         let uu____14372 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____14372
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___177_14368.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___177_14368.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___177_14368.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____14371;
                         FStar_TypeChecker_Common.element =
                           (uu___177_14368.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___177_14368.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.scope =
                           (uu___177_14368.FStar_TypeChecker_Common.scope);
                         FStar_TypeChecker_Common.reason =
                           (uu___177_14368.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___177_14368.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___177_14368.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____14365 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____14373,FStar_Syntax_Syntax.Comp uu____14374) ->
                     let uu____14375 =
                       ((FStar_Syntax_Util.is_ml_comp c11) &&
                          (FStar_Syntax_Util.is_ml_comp c21))
                         ||
                         ((FStar_Syntax_Util.is_total_comp c11) &&
                            ((FStar_Syntax_Util.is_total_comp c21) ||
                               (FStar_Syntax_Util.is_ml_comp c21)))
                        in
                     if uu____14375
                     then
                       let uu____14376 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21) None
                           "result type"
                          in
                       solve_t env uu____14376 wl
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
                           (let uu____14386 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____14386
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____14388 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____14388 with
                            | None  ->
                                let uu____14390 =
                                  ((FStar_Syntax_Util.is_ghost_effect
                                      c12.FStar_Syntax_Syntax.effect_name)
                                     &&
                                     (FStar_Syntax_Util.is_pure_effect
                                        c22.FStar_Syntax_Syntax.effect_name))
                                    &&
                                    (let uu____14391 =
                                       FStar_TypeChecker_Normalize.normalize
                                         [FStar_TypeChecker_Normalize.Eager_unfolding;
                                         FStar_TypeChecker_Normalize.UnfoldUntil
                                           FStar_Syntax_Syntax.Delta_constant]
                                         env
                                         c22.FStar_Syntax_Syntax.result_typ
                                        in
                                     FStar_Syntax_Util.non_informative
                                       uu____14391)
                                   in
                                if uu____14390
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
                                  (let uu____14394 =
                                     let uu____14395 =
                                       FStar_Syntax_Print.lid_to_string
                                         c12.FStar_Syntax_Syntax.effect_name
                                        in
                                     let uu____14396 =
                                       FStar_Syntax_Print.lid_to_string
                                         c22.FStar_Syntax_Syntax.effect_name
                                        in
                                     FStar_Util.format2
                                       "incompatible monad ordering: %s </: %s"
                                       uu____14395 uu____14396
                                      in
                                   giveup env uu____14394 orig)
                            | Some edge -> solve_sub c12 edge c22))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t -> Prims.string =
  fun g  ->
    let uu____14401 =
      FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits
        (FStar_List.map
           (fun uu____14421  ->
              match uu____14421 with
              | (uu____14432,uu____14433,u,uu____14435,uu____14436,uu____14437)
                  -> FStar_Syntax_Print.uvar_to_string u))
       in
    FStar_All.pipe_right uu____14401 (FStar_String.concat ", ")
  
let ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string
  =
  fun ineqs  ->
    let vars =
      let uu____14466 =
        FStar_All.pipe_right (fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____14466 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____14476 =
        FStar_All.pipe_right (snd ineqs)
          (FStar_List.map
             (fun uu____14488  ->
                match uu____14488 with
                | (u1,u2) ->
                    let uu____14493 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____14494 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____14493 uu____14494))
         in
      FStar_All.pipe_right uu____14476 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____14506,[])) -> "{}"
      | uu____14519 ->
          let form =
            match g.FStar_TypeChecker_Env.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____14529 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Implicits")))
                    ||
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       FStar_Options.Extreme)
                   in
                if uu____14529
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry =
            let uu____14532 =
              FStar_List.map
                (fun uu____14536  ->
                   match uu____14536 with
                   | (uu____14539,x) -> prob_to_string env x)
                g.FStar_TypeChecker_Env.deferred
               in
            FStar_All.pipe_right uu____14532 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____14543 =
            ineqs_to_string g.FStar_TypeChecker_Env.univ_ineqs  in
          FStar_Util.format4
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form carry uu____14543 imps
  
let new_t_problem env lhs rel rhs elt loc =
  let reason =
    let uu____14581 =
      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
        (FStar_Options.Other "ExplainRel")
       in
    if uu____14581
    then
      let uu____14582 = FStar_TypeChecker_Normalize.term_to_string env lhs
         in
      let uu____14583 = FStar_TypeChecker_Normalize.term_to_string env rhs
         in
      FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____14582
        (rel_to_string rel) uu____14583
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
            let uu____14603 =
              let uu____14605 = FStar_TypeChecker_Env.get_range env  in
              FStar_All.pipe_left (fun _0_86  -> Some _0_86) uu____14605  in
            FStar_Syntax_Syntax.new_bv uu____14603 t1  in
          let env1 = FStar_TypeChecker_Env.push_bv env x  in
          let p =
            let uu____14611 =
              let uu____14613 = FStar_Syntax_Syntax.bv_to_name x  in
              FStar_All.pipe_left (fun _0_87  -> Some _0_87) uu____14613  in
            let uu____14615 = FStar_TypeChecker_Env.get_range env1  in
            new_t_problem env1 t1 rel t2 uu____14611 uu____14615  in
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
          let uu____14638 = FStar_Options.eager_inference ()  in
          if uu____14638
          then
            let uu___178_14639 = probs  in
            {
              attempting = (uu___178_14639.attempting);
              wl_deferred = (uu___178_14639.wl_deferred);
              ctr = (uu___178_14639.ctr);
              defer_ok = false;
              smt_ok = (uu___178_14639.smt_ok);
              tcenv = (uu___178_14639.tcenv)
            }
          else probs  in
        let tx = FStar_Unionfind.new_transaction ()  in
        let sol = solve env probs1  in
        match sol with
        | Success deferred -> (FStar_Unionfind.commit tx; Some deferred)
        | Failed (d,s) ->
            (FStar_Unionfind.rollback tx;
             (let uu____14650 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ExplainRel")
                 in
              if uu____14650
              then
                let uu____14651 = explain env d s  in
                FStar_All.pipe_left FStar_Util.print_string uu____14651
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
          ((let uu____14661 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____14661
            then
              let uu____14662 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____14662
            else ());
           (let f1 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Normalize.Beta;
                FStar_TypeChecker_Normalize.Eager_unfolding;
                FStar_TypeChecker_Normalize.Simplify] env f
               in
            (let uu____14666 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____14666
             then
               let uu____14667 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____14667
             else ());
            (let f2 =
               let uu____14670 =
                 let uu____14671 = FStar_Syntax_Util.unmeta f1  in
                 uu____14671.FStar_Syntax_Syntax.n  in
               match uu____14670 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____14675 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___179_14676 = g  in
             {
               FStar_TypeChecker_Env.guard_f = f2;
               FStar_TypeChecker_Env.deferred =
                 (uu___179_14676.FStar_TypeChecker_Env.deferred);
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___179_14676.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___179_14676.FStar_TypeChecker_Env.implicits)
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
            let uu____14691 =
              let uu____14692 =
                let uu____14693 =
                  let uu____14694 =
                    FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst
                     in
                  FStar_All.pipe_right uu____14694
                    (fun _0_88  -> FStar_TypeChecker_Common.NonTrivial _0_88)
                   in
                {
                  FStar_TypeChecker_Env.guard_f = uu____14693;
                  FStar_TypeChecker_Env.deferred = d;
                  FStar_TypeChecker_Env.univ_ineqs = ([], []);
                  FStar_TypeChecker_Env.implicits = []
                }  in
              simplify_guard env uu____14692  in
            FStar_All.pipe_left (fun _0_89  -> Some _0_89) uu____14691
  
let with_guard_no_simp env prob dopt =
  match dopt with
  | None  -> None
  | Some d ->
      let uu____14727 =
        let uu____14728 =
          let uu____14729 =
            FStar_All.pipe_right (p_guard prob) FStar_Pervasives.fst  in
          FStar_All.pipe_right uu____14729
            (fun _0_90  -> FStar_TypeChecker_Common.NonTrivial _0_90)
           in
        {
          FStar_TypeChecker_Env.guard_f = uu____14728;
          FStar_TypeChecker_Env.deferred = d;
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits = []
        }  in
      Some uu____14727
  
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
          (let uu____14755 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14755
           then
             let uu____14756 = FStar_Syntax_Print.term_to_string t1  in
             let uu____14757 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s\n" uu____14756
               uu____14757
           else ());
          (let prob =
             let uu____14760 =
               let uu____14763 = FStar_TypeChecker_Env.get_range env  in
               new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None
                 uu____14763
                in
             FStar_All.pipe_left
               (fun _0_91  -> FStar_TypeChecker_Common.TProb _0_91)
               uu____14760
              in
           let g =
             let uu____14768 =
               let uu____14770 = singleton' env prob smt_ok  in
               solve_and_commit env uu____14770 (fun uu____14771  -> None)
                in
             FStar_All.pipe_left (with_guard env prob) uu____14768  in
           g)
  
let teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____14785 = try_teq true env t1 t2  in
        match uu____14785 with
        | None  ->
            let uu____14787 =
              let uu____14788 =
                let uu____14791 =
                  FStar_TypeChecker_Err.basic_type_error env None t2 t1  in
                let uu____14792 = FStar_TypeChecker_Env.get_range env  in
                (uu____14791, uu____14792)  in
              FStar_Errors.Error uu____14788  in
            raise uu____14787
        | Some g ->
            ((let uu____14795 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____14795
              then
                let uu____14796 = FStar_Syntax_Print.term_to_string t1  in
                let uu____14797 = FStar_Syntax_Print.term_to_string t2  in
                let uu____14798 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____14796
                  uu____14797 uu____14798
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
          (let uu____14814 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____14814
           then
             let uu____14815 =
               FStar_TypeChecker_Normalize.term_to_string env t1  in
             let uu____14816 =
               FStar_TypeChecker_Normalize.term_to_string env t2  in
             FStar_Util.print2 "try_subtype of %s and %s\n" uu____14815
               uu____14816
           else ());
          (let uu____14818 =
             new_t_prob env t1 FStar_TypeChecker_Common.SUB t2  in
           match uu____14818 with
           | (prob,x) ->
               let g =
                 let uu____14826 =
                   let uu____14828 = singleton' env prob smt_ok  in
                   solve_and_commit env uu____14828
                     (fun uu____14829  -> None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____14826  in
               ((let uu____14835 =
                   (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     && (FStar_Util.is_some g)
                    in
                 if uu____14835
                 then
                   let uu____14836 =
                     FStar_TypeChecker_Normalize.term_to_string env t1  in
                   let uu____14837 =
                     FStar_TypeChecker_Normalize.term_to_string env t2  in
                   let uu____14838 =
                     let uu____14839 = FStar_Util.must g  in
                     guard_to_string env uu____14839  in
                   FStar_Util.print3
                     "try_subtype succeeded: %s <: %s\n\tguard is %s\n"
                     uu____14836 uu____14837 uu____14838
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
          let uu____14863 = FStar_TypeChecker_Env.get_range env  in
          let uu____14864 =
            FStar_TypeChecker_Err.basic_type_error env (Some e) t2 t1  in
          FStar_Errors.err uu____14863 uu____14864
  
let sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp -> FStar_TypeChecker_Env.guard_t option
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        (let uu____14876 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____14876
         then
           let uu____14877 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____14878 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print2 "sub_comp of %s and %s\n" uu____14877
             uu____14878
         else ());
        (let rel =
           if env.FStar_TypeChecker_Env.use_eq
           then FStar_TypeChecker_Common.EQ
           else FStar_TypeChecker_Common.SUB  in
         let prob =
           let uu____14883 =
             let uu____14886 = FStar_TypeChecker_Env.get_range env  in
             new_problem env c1 rel c2 None uu____14886 "sub_comp"  in
           FStar_All.pipe_left
             (fun _0_92  -> FStar_TypeChecker_Common.CProb _0_92) uu____14883
            in
         let uu____14889 =
           let uu____14891 = singleton env prob  in
           solve_and_commit env uu____14891 (fun uu____14892  -> None)  in
         FStar_All.pipe_left (with_guard env prob) uu____14889)
  
let solve_universe_inequalities' :
  FStar_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> Prims.unit
  =
  fun tx  ->
    fun env  ->
      fun uu____14911  ->
        match uu____14911 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Unionfind.rollback tx;
              (let uu____14936 =
                 let uu____14937 =
                   let uu____14940 =
                     let uu____14941 = FStar_Syntax_Print.univ_to_string u1
                        in
                     let uu____14942 = FStar_Syntax_Print.univ_to_string u2
                        in
                     FStar_Util.format2 "Universe %s and %s are incompatible"
                       uu____14941 uu____14942
                      in
                   let uu____14943 = FStar_TypeChecker_Env.get_range env  in
                   (uu____14940, uu____14943)  in
                 FStar_Errors.Error uu____14937  in
               raise uu____14936)
               in
            let equiv v1 v' =
              let uu____14951 =
                let uu____14954 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____14955 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____14954, uu____14955)  in
              match uu____14951 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Unionfind.equivalent v0 v0'
              | uu____14963 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____14977 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____14977 with
                      | FStar_Syntax_Syntax.U_unif uu____14981 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____14992  ->
                                    match uu____14992 with
                                    | (u,v') ->
                                        let uu____14998 = equiv v1 v'  in
                                        if uu____14998
                                        then
                                          let uu____15000 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____15000 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____15010 -> []))
               in
            let uu____15013 =
              let wl =
                let uu___180_15016 = empty_worklist env  in
                {
                  attempting = (uu___180_15016.attempting);
                  wl_deferred = (uu___180_15016.wl_deferred);
                  ctr = (uu___180_15016.ctr);
                  defer_ok = false;
                  smt_ok = (uu___180_15016.smt_ok);
                  tcenv = (uu___180_15016.tcenv)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____15023  ->
                      match uu____15023 with
                      | (lb,v1) ->
                          let uu____15028 =
                            solve_universe_eq (~- (Prims.parse_int "1")) wl
                              lb v1
                             in
                          (match uu____15028 with
                           | USolved wl1 -> ()
                           | uu____15030 -> fail lb v1)))
               in
            let rec check_ineq uu____15036 =
              match uu____15036 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____15043) -> true
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
                      uu____15055,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____15057,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____15062) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____15066,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____15071 -> false)
               in
            let uu____15074 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____15080  ->
                      match uu____15080 with
                      | (u,v1) ->
                          let uu____15085 = check_ineq (u, v1)  in
                          if uu____15085
                          then true
                          else
                            ((let uu____15088 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____15088
                              then
                                let uu____15089 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____15090 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____15089
                                  uu____15090
                              else ());
                             false)))
               in
            if uu____15074
            then ()
            else
              ((let uu____15094 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____15094
                then
                  ((let uu____15096 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____15096);
                   FStar_Unionfind.rollback tx;
                   (let uu____15102 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____15102))
                else ());
               (let uu____15108 =
                  let uu____15109 =
                    let uu____15112 = FStar_TypeChecker_Env.get_range env  in
                    ("Failed to solve universe inequalities for inductives",
                      uu____15112)
                     in
                  FStar_Errors.Error uu____15109  in
                raise uu____15108))
  
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
      let fail uu____15145 =
        match uu____15145 with
        | (d,s) ->
            let msg = explain env d s  in
            raise (FStar_Errors.Error (msg, (p_loc d)))
         in
      let wl = wl_of_guard env g.FStar_TypeChecker_Env.deferred  in
      (let uu____15155 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____15155
       then
         let uu____15156 = wl_to_string wl  in
         let uu____15157 =
           FStar_Util.string_of_int
             (FStar_List.length g.FStar_TypeChecker_Env.implicits)
            in
         FStar_Util.print2
           "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n"
           uu____15156 uu____15157
       else ());
      (let g1 =
         let uu____15169 = solve_and_commit env wl fail  in
         match uu____15169 with
         | Some [] ->
             let uu___181_15176 = g  in
             {
               FStar_TypeChecker_Env.guard_f =
                 (uu___181_15176.FStar_TypeChecker_Env.guard_f);
               FStar_TypeChecker_Env.deferred = [];
               FStar_TypeChecker_Env.univ_ineqs =
                 (uu___181_15176.FStar_TypeChecker_Env.univ_ineqs);
               FStar_TypeChecker_Env.implicits =
                 (uu___181_15176.FStar_TypeChecker_Env.implicits)
             }
         | uu____15179 ->
             failwith "impossible: Unexpected deferred constraints remain"
          in
       solve_universe_inequalities env g1.FStar_TypeChecker_Env.univ_ineqs;
       (let uu___182_15182 = g1  in
        {
          FStar_TypeChecker_Env.guard_f =
            (uu___182_15182.FStar_TypeChecker_Env.guard_f);
          FStar_TypeChecker_Env.deferred =
            (uu___182_15182.FStar_TypeChecker_Env.deferred);
          FStar_TypeChecker_Env.univ_ineqs = ([], []);
          FStar_TypeChecker_Env.implicits =
            (uu___182_15182.FStar_TypeChecker_Env.implicits)
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
            let uu___183_15208 = g1  in
            {
              FStar_TypeChecker_Env.guard_f =
                FStar_TypeChecker_Common.Trivial;
              FStar_TypeChecker_Env.deferred =
                (uu___183_15208.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___183_15208.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___183_15208.FStar_TypeChecker_Env.implicits)
            }  in
          let uu____15209 =
            let uu____15210 = FStar_TypeChecker_Env.should_verify env  in
            Prims.op_Negation uu____15210  in
          if uu____15209
          then Some ret_g
          else
            (match g1.FStar_TypeChecker_Env.guard_f with
             | FStar_TypeChecker_Common.Trivial  -> Some ret_g
             | FStar_TypeChecker_Common.NonTrivial vc ->
                 ((let uu____15216 =
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Norm"))
                       ||
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "SMTQuery"))
                      in
                   if uu____15216
                   then
                     let uu____15217 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____15218 =
                       let uu____15219 = FStar_Syntax_Print.term_to_string vc
                          in
                       FStar_Util.format1 "Before normalization VC=\n%s\n"
                         uu____15219
                        in
                     FStar_Errors.diag uu____15217 uu____15218
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
                         ((let uu____15228 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____15228
                           then
                             let uu____15229 =
                               FStar_TypeChecker_Env.get_range env  in
                             let uu____15230 =
                               let uu____15231 =
                                 FStar_Syntax_Print.term_to_string vc2  in
                               FStar_Util.format1 "Checking VC=\n%s\n"
                                 uu____15231
                                in
                             FStar_Errors.diag uu____15229 uu____15230
                           else ());
                          (let vcs =
                             let uu____15237 = FStar_Options.use_tactics ()
                                in
                             if uu____15237
                             then
                               (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                 env vc2
                             else [(env, vc2)]  in
                           FStar_All.pipe_right vcs
                             (FStar_List.iter
                                (fun uu____15251  ->
                                   match uu____15251 with
                                   | (env1,goal) ->
                                       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                         use_env_range_msg env1 goal)));
                          Some ret_g))))
  
let discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15262 = discharge_guard' None env g false  in
      match uu____15262 with
      | Some g1 -> g1
      | None  ->
          let uu____15267 =
            let uu____15268 =
              let uu____15271 = FStar_TypeChecker_Env.get_range env  in
              ("Expected a trivial pre-condition", uu____15271)  in
            FStar_Errors.Error uu____15268  in
          raise uu____15267
  
let discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t
  =
  fun env  ->
    fun g  ->
      let uu____15278 = discharge_guard' None env g true  in
      match uu____15278 with
      | Some g1 -> g1
      | None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let resolve_implicits :
  FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t =
  fun g  ->
    let unresolved u =
      let uu____15298 = FStar_Unionfind.find u  in
      match uu____15298 with
      | FStar_Syntax_Syntax.Uvar  -> true
      | uu____15307 -> false  in
    let rec until_fixpoint acc implicits =
      let uu____15322 = acc  in
      match uu____15322 with
      | (out,changed) ->
          (match implicits with
           | [] ->
               if Prims.op_Negation changed
               then out
               else until_fixpoint ([], false) out
           | hd1::tl1 ->
               let uu____15368 = hd1  in
               (match uu____15368 with
                | (uu____15375,env,u,tm,k,r) ->
                    let uu____15381 = unresolved u  in
                    if uu____15381
                    then until_fixpoint ((hd1 :: out), changed) tl1
                    else
                      (let env1 =
                         FStar_TypeChecker_Env.set_expected_typ env k  in
                       let tm1 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta] env1 tm
                          in
                       (let uu____15399 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env1)
                            (FStar_Options.Other "RelCheck")
                           in
                        if uu____15399
                        then
                          let uu____15400 =
                            FStar_Syntax_Print.uvar_to_string u  in
                          let uu____15404 =
                            FStar_Syntax_Print.term_to_string tm1  in
                          let uu____15405 =
                            FStar_Syntax_Print.term_to_string k  in
                          FStar_Util.print3
                            "Checking uvar %s resolved to %s at type %s\n"
                            uu____15400 uu____15404 uu____15405
                        else ());
                       (let uu____15407 =
                          env1.FStar_TypeChecker_Env.type_of
                            (let uu___184_15411 = env1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___184_15411.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___184_15411.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___184_15411.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___184_15411.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___184_15411.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___184_15411.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___184_15411.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___184_15411.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___184_15411.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___184_15411.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___184_15411.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___184_15411.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___184_15411.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___184_15411.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___184_15411.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___184_15411.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___184_15411.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___184_15411.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___184_15411.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___184_15411.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___184_15411.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___184_15411.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts = true;
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___184_15411.FStar_TypeChecker_Env.qname_and_index)
                             }) tm1
                           in
                        match uu____15407 with
                        | (uu____15412,uu____15413,g1) ->
                            let g2 =
                              if env1.FStar_TypeChecker_Env.is_pattern
                              then
                                let uu___185_15416 = g1  in
                                {
                                  FStar_TypeChecker_Env.guard_f =
                                    FStar_TypeChecker_Common.Trivial;
                                  FStar_TypeChecker_Env.deferred =
                                    (uu___185_15416.FStar_TypeChecker_Env.deferred);
                                  FStar_TypeChecker_Env.univ_ineqs =
                                    (uu___185_15416.FStar_TypeChecker_Env.univ_ineqs);
                                  FStar_TypeChecker_Env.implicits =
                                    (uu___185_15416.FStar_TypeChecker_Env.implicits)
                                }
                              else g1  in
                            let g' =
                              let uu____15419 =
                                discharge_guard'
                                  (Some
                                     (fun uu____15423  ->
                                        FStar_Syntax_Print.term_to_string tm1))
                                  env1 g2 true
                                 in
                              match uu____15419 with
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
    let uu___186_15438 = g  in
    let uu____15439 =
      until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits  in
    {
      FStar_TypeChecker_Env.guard_f =
        (uu___186_15438.FStar_TypeChecker_Env.guard_f);
      FStar_TypeChecker_Env.deferred =
        (uu___186_15438.FStar_TypeChecker_Env.deferred);
      FStar_TypeChecker_Env.univ_ineqs =
        (uu___186_15438.FStar_TypeChecker_Env.univ_ineqs);
      FStar_TypeChecker_Env.implicits = uu____15439
    }
  
let force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.guard_t -> Prims.unit =
  fun env  ->
    fun g  ->
      let g1 =
        let uu____15467 = solve_deferred_constraints env g  in
        FStar_All.pipe_right uu____15467 resolve_implicits  in
      match g1.FStar_TypeChecker_Env.implicits with
      | [] ->
          let uu____15474 = discharge_guard env g1  in
          FStar_All.pipe_left FStar_Pervasives.ignore uu____15474
      | (reason,uu____15476,uu____15477,e,t,r)::uu____15481 ->
          let uu____15495 =
            let uu____15496 = FStar_Syntax_Print.term_to_string t  in
            let uu____15497 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format3
              "Failed to resolve implicit argument of type '%s' introduced in %s because %s"
              uu____15496 uu____15497 reason
             in
          FStar_Errors.err r uu____15495
  
let universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Env.guard_t
  =
  fun u1  ->
    fun u2  ->
      let uu___187_15504 = trivial_guard  in
      {
        FStar_TypeChecker_Env.guard_f =
          (uu___187_15504.FStar_TypeChecker_Env.guard_f);
        FStar_TypeChecker_Env.deferred =
          (uu___187_15504.FStar_TypeChecker_Env.deferred);
        FStar_TypeChecker_Env.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Env.implicits =
          (uu___187_15504.FStar_TypeChecker_Env.implicits)
      }
  
let teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____15522 = try_teq false env t1 t2  in
        match uu____15522 with
        | None  -> false
        | Some g ->
            let uu____15525 = discharge_guard' None env g false  in
            (match uu____15525 with
             | Some uu____15529 -> true
             | None  -> false)
  