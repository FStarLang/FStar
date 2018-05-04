open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2[@@deriving show]
let (report : FStar_TypeChecker_Env.env -> Prims.string Prims.list -> unit) =
  fun env  ->
    fun errs  ->
      let uu____21 = FStar_TypeChecker_Env.get_range env  in
      let uu____22 = FStar_TypeChecker_Err.failed_to_prove_specification errs
         in
      FStar_Errors.log_issue uu____21 uu____22
  
let (new_implicit_var_aux :
  Prims.string ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.binding Prims.list ->
        (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
          FStar_Pervasives_Native.tuple2 Prims.list ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            (FStar_Syntax_Syntax.ctx_uvar,FStar_Syntax_Syntax.term'
                                            FStar_Syntax_Syntax.syntax)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun r  ->
      fun gamma  ->
        fun binders  ->
          fun k  ->
            let ctx_uvar =
              let uu____79 = FStar_Syntax_Unionfind.fresh ()  in
              {
                FStar_Syntax_Syntax.ctx_uvar_head = uu____79;
                FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                FStar_Syntax_Syntax.ctx_uvar_typ = k;
                FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                FStar_Syntax_Syntax.ctx_uvar_should_check = true;
                FStar_Syntax_Syntax.ctx_uvar_range = r
              }  in
            FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r true
              gamma binders;
            (let uu____91 =
               FStar_Syntax_Syntax.mk
                 (FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, []))
                 FStar_Pervasives_Native.None r
                in
             (ctx_uvar, uu____91))
  
let (new_implicit_var :
  Prims.string ->
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,(FStar_Syntax_Syntax.ctx_uvar,FStar_Range.range)
                                      FStar_Pervasives_Native.tuple2
                                      Prims.list,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          let uu____130 =
            FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid  in
          match uu____130 with
          | FStar_Pervasives_Native.Some (uu____153::(tm,uu____155)::[]) ->
              let t =
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                  FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                 in
              (t, [], FStar_TypeChecker_Rel.trivial_guard)
          | uu____205 ->
              let binders = FStar_TypeChecker_Env.all_binders env  in
              let uu____217 =
                new_implicit_var_aux reason r env.FStar_TypeChecker_Env.gamma
                  binders k
                 in
              (match uu____217 with
               | (ctx_uvar,t) ->
                   let g =
                     let uu___122_243 = FStar_TypeChecker_Rel.trivial_guard
                        in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         (uu___122_243.FStar_TypeChecker_Env.guard_f);
                       FStar_TypeChecker_Env.deferred =
                         (uu___122_243.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___122_243.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         [(reason, t, ctx_uvar, r, true)]
                     }  in
                   (t, [(ctx_uvar, r)], g))
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____293 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____339  ->
                  match uu____339 with
                  | (uu____344,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____293 with
        | (solve_now,defer) ->
            ((let uu____373 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____373
              then
                (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                 FStar_List.iter
                   (fun uu____384  ->
                      match uu____384 with
                      | (s,p) ->
                          let uu____391 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____391) solve_now;
                 FStar_Util.print_string " ...DEFERRED THE REST:\n";
                 FStar_List.iter
                   (fun uu____402  ->
                      match uu____402 with
                      | (s,p) ->
                          let uu____409 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____409) defer;
                 FStar_Util.print_string "END\n")
              else ());
             (let g1 =
                FStar_TypeChecker_Rel.solve_deferred_constraints env
                  (let uu___123_413 = g  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___123_413.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = solve_now;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___123_413.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___123_413.FStar_TypeChecker_Env.implicits)
                   })
                 in
              let g2 =
                let uu___124_415 = g1  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___124_415.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred = defer;
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___124_415.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits =
                    (uu___124_415.FStar_TypeChecker_Env.implicits)
                }  in
              (let uu____417 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____417
               then
                 let uu____418 = FStar_Syntax_Print.binders_to_string ", " xs
                    in
                 FStar_Util.print1
                   "Starting to close implicits with binders {%s}\n"
                   uu____418
               else ());
              (let uu____421 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____421
               then
                 let uu____422 = FStar_Syntax_Print.binders_to_string ", " xs
                    in
                 let uu____423 = FStar_TypeChecker_Rel.guard_to_string env g2
                    in
                 FStar_Util.print2
                   "Closed implicits with binders {%s}; guard is\n\t%s\n"
                   uu____422 uu____423
               else ());
              g2))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____438 =
        let uu____439 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____439  in
      if uu____438
      then
        let us =
          let uu____441 =
            let uu____444 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____444
             in
          FStar_All.pipe_right uu____441 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____455 =
            let uu____460 =
              let uu____461 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____461
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____460)  in
          FStar_Errors.log_issue r uu____455);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____478  ->
      match uu____478 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____488;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____490;
          FStar_Syntax_Syntax.lbpos = uu____491;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____524 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____524 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____561) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____568) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____623) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____655 = FStar_Options.ml_ish ()  in
                                if uu____655
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____672 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____672
                            then
                              let uu____673 = FStar_Range.string_of_range r
                                 in
                              let uu____674 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____673 uu____674
                            else ());
                           FStar_Util.Inl t2)
                      | uu____676 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____678 = aux e1  in
                      match uu____678 with
                      | FStar_Util.Inr c ->
                          let uu____684 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____684
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____686 =
                               let uu____691 =
                                 let uu____692 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____692
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____691)
                                in
                             FStar_Errors.raise_error uu____686 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____696 ->
               let uu____697 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____697 with
                | (univ_vars2,t2) -> (univ_vars2, t2, false)))
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____791 =
              let uu____796 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____796 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____801;
                  FStar_Syntax_Syntax.vars = uu____802;_} ->
                  let uu____805 = FStar_Syntax_Util.type_u ()  in
                  (match uu____805 with
                   | (t,uu____815) ->
                       let uu____816 =
                         let uu____829 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var "pattern bv type" uu____829 env1 t
                          in
                       (match uu____816 with | (t1,uu____835,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____791 with
            | (t_x,guard) ->
                ((let uu___125_857 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_857.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_857.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = t_x
                  }), guard)
             in
          let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr,FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu____932 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____940) ->
                let uu____945 = FStar_Syntax_Util.type_u ()  in
                (match uu____945 with
                 | (k,uu____971) ->
                     let uu____972 =
                       let uu____985 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var "pat_dot_term type" uu____985 env1 k
                        in
                     (match uu____972 with
                      | (t,uu____1007,g) ->
                          let x1 =
                            let uu___126_1022 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_1022.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_1022.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1023 =
                            let uu____1036 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var "pat_dot_term" uu____1036 env1 t
                             in
                          (match uu____1023 with
                           | (e,uu____1058,g') ->
                               let p2 =
                                 let uu___127_1075 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___127_1075.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1078 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1078, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1086 = check_bv env1 x  in
                (match uu____1086 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____1125 = check_bv env1 x  in
                (match uu____1125 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____1180 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1314  ->
                          fun uu____1315  ->
                            match (uu____1314, uu____1315) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1513 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1513 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1589 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1589, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1180 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1720 =
                         let uu____1725 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1726 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1725 uu____1726
                          in
                       uu____1720 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1743 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1754 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1765 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1743, uu____1754, uu____1765, env2, e, guard,
                       (let uu___128_1783 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___128_1783.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____1883  ->
                       match uu____1883 with
                       | (p2,imp) ->
                           let uu____1902 = elaborate_pat env1 p2  in
                           (uu____1902, imp)) pats
                   in
                let uu____1907 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____1907 with
                 | (uu____1914,t) ->
                     let uu____1916 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____1916 with
                      | (f,uu____1932) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2058::uu____2059) ->
                                let uu____2102 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2102
                            | (uu____2111::uu____2112,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2190  ->
                                        match uu____2190 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2217 =
                                                     let uu____2220 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2220
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2217
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2222 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2222, true)
                                             | uu____2227 ->
                                                 let uu____2230 =
                                                   let uu____2235 =
                                                     let uu____2236 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2236
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2235)
                                                    in
                                                 let uu____2237 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2230 uu____2237)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2311,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2312)) when p_imp ->
                                     let uu____2315 = aux formals' pats'  in
                                     (p2, true) :: uu____2315
                                 | (uu____2332,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2340 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2340
                                        in
                                     let uu____2341 = aux formals' pats2  in
                                     (p3, true) :: uu____2341
                                 | (uu____2358,imp) ->
                                     let uu____2364 =
                                       let uu____2371 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2371)  in
                                     let uu____2374 = aux formals' pats'  in
                                     uu____2364 :: uu____2374)
                             in
                          let uu___129_2389 = p1  in
                          let uu____2392 =
                            let uu____2393 =
                              let uu____2406 = aux f pats1  in
                              (fv, uu____2406)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2393  in
                          {
                            FStar_Syntax_Syntax.v = uu____2392;
                            FStar_Syntax_Syntax.p =
                              (uu___129_2389.FStar_Syntax_Syntax.p)
                          }))
            | uu____2423 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2465 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2465 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2523 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2523 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2549 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2549
                       p3.FStar_Syntax_Syntax.p
                 | uu____2572 -> (b, a, w, arg, guard, p3))
             in
          let uu____2581 = one_pat true env p  in
          match uu____2581 with
          | (b,uu____2611,uu____2612,tm,guard,p1) -> (b, tm, guard, p1)
  
let (decorate_pattern :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      fun exp  ->
        let qq = p  in
        let rec aux p1 e =
          let pkg q = FStar_Syntax_Syntax.withinfo q p1.FStar_Syntax_Syntax.p
             in
          let e1 = FStar_Syntax_Util.unmeta e  in
          match ((p1.FStar_Syntax_Syntax.v), (e1.FStar_Syntax_Syntax.n)) with
          | (uu____2674,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2676)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2681,uu____2682) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2686 =
                    let uu____2687 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2688 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2687 uu____2688
                     in
                  failwith uu____2686)
               else ();
               (let uu____2691 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2691
                then
                  let uu____2692 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2693 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2692
                    uu____2693
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___130_2697 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___130_2697.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___130_2697.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2701 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2701
                then
                  let uu____2702 =
                    let uu____2703 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2704 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2703 uu____2704
                     in
                  failwith uu____2702
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___131_2708 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___131_2708.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___131_2708.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2710),uu____2711) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2735 =
                  let uu____2736 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2736  in
                if uu____2735
                then
                  let uu____2737 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2737
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2756;
                FStar_Syntax_Syntax.vars = uu____2757;_},args))
              ->
              ((let uu____2796 =
                  let uu____2797 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2797 Prims.op_Negation  in
                if uu____2796
                then
                  let uu____2798 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2798
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2936)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3011) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3048) ->
                           let pat =
                             let uu____3070 = aux argpat e2  in
                             let uu____3071 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3070, uu____3071)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3076 ->
                      let uu____3099 =
                        let uu____3100 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3101 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3100 uu____3101
                         in
                      failwith uu____3099
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3111;
                     FStar_Syntax_Syntax.vars = uu____3112;_},uu____3113);
                FStar_Syntax_Syntax.pos = uu____3114;
                FStar_Syntax_Syntax.vars = uu____3115;_},args))
              ->
              ((let uu____3158 =
                  let uu____3159 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3159 Prims.op_Negation  in
                if uu____3158
                then
                  let uu____3160 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3160
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3298)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3373) ->
                           let x =
                             FStar_Syntax_Syntax.new_bv
                               (FStar_Pervasives_Native.Some
                                  (p1.FStar_Syntax_Syntax.p))
                               FStar_Syntax_Syntax.tun
                              in
                           let q =
                             FStar_Syntax_Syntax.withinfo
                               (FStar_Syntax_Syntax.Pat_dot_term (x, e2))
                               p1.FStar_Syntax_Syntax.p
                              in
                           match_args ((q, true) :: matched_pats) args2
                             argpats2
                       | ((e2,imp),uu____3410) ->
                           let pat =
                             let uu____3432 = aux argpat e2  in
                             let uu____3433 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3432, uu____3433)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3438 ->
                      let uu____3461 =
                        let uu____3462 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3463 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3462 uu____3463
                         in
                      failwith uu____3461
                   in
                match_args [] args argpats))
          | uu____3470 ->
              let uu____3475 =
                let uu____3476 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3477 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3478 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3476 uu____3477 uu____3478
                 in
              failwith uu____3475
           in
        aux p exp
  
let rec (decorated_pattern_as_term :
  FStar_Syntax_Syntax.pat ->
    (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  =
  fun pat  ->
    let mk1 f =
      FStar_Syntax_Syntax.mk f FStar_Pervasives_Native.None
        pat.FStar_Syntax_Syntax.p
       in
    let pat_as_arg uu____3521 =
      match uu____3521 with
      | (p,i) ->
          let uu____3538 = decorated_pattern_as_term p  in
          (match uu____3538 with
           | (vars,te) ->
               let uu____3561 =
                 let uu____3566 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3566)  in
               (vars, uu____3561))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3580 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3580)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3584 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3584)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3588 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3588)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3609 =
          let uu____3626 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3626 FStar_List.unzip  in
        (match uu____3609 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3746 =
               let uu____3747 =
                 let uu____3748 =
                   let uu____3763 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3763, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3748  in
               mk1 uu____3747  in
             (vars1, uu____3746))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3799,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3809,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3823 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3845)::[] -> wp
      | uu____3862 ->
          let uu____3871 =
            let uu____3872 =
              let uu____3873 =
                FStar_List.map
                  (fun uu____3883  ->
                     match uu____3883 with
                     | (x,uu____3889) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____3873 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3872
             in
          failwith uu____3871
       in
    let uu____3892 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____3892, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3908 = destruct_comp c  in
        match uu____3908 with
        | (u,uu____3916,wp) ->
            let uu____3918 =
              let uu____3927 =
                let uu____3934 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____3934  in
              [uu____3927]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3918;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3962 =
          let uu____3969 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____3970 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____3969 uu____3970  in
        match uu____3962 with | (m,uu____3972,uu____3973) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3989 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____3989
        then FStar_Parser_Const.effect_Tot_lid
        else
          join_effects env c1.FStar_Syntax_Syntax.eff_name
            c2.FStar_Syntax_Syntax.eff_name
  
let (lift_and_destruct :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        ((FStar_Syntax_Syntax.eff_decl,FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.term)
           FStar_Pervasives_Native.tuple3,(FStar_Syntax_Syntax.universe,
                                            FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
                                            FStar_Pervasives_Native.tuple3,
          (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.tuple3)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let c11 = FStar_TypeChecker_Env.unfold_effect_abbrev env c1  in
        let c21 = FStar_TypeChecker_Env.unfold_effect_abbrev env c2  in
        let uu____4032 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4032 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4069 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4069 with
             | (a,kwp) ->
                 let uu____4100 = destruct_comp m1  in
                 let uu____4107 = destruct_comp m2  in
                 ((md, a, kwp), uu____4100, uu____4107))
  
let (is_pure_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid
  
let (is_pure_or_ghost_effect :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> Prims.bool) =
  fun env  ->
    fun l  ->
      let l1 = FStar_TypeChecker_Env.norm_eff_name env l  in
      (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid) ||
        (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GHOST_lid)
  
let (mk_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun wp  ->
          fun flags1  ->
            let uu____4187 =
              let uu____4188 =
                let uu____4197 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4197]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4188;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4187
  
let (mk_comp :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  = fun md  -> mk_comp_l md.FStar_Syntax_Syntax.mname 
let (lax_mk_tot_or_comp_l :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.universe ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun mname  ->
    fun u_result  ->
      fun result  ->
        fun flags1  ->
          let uu____4273 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4273
          then
            FStar_Syntax_Syntax.mk_Total' result
              (FStar_Pervasives_Native.Some u_result)
          else mk_comp_l mname u_result result FStar_Syntax_Syntax.tun flags1
  
let (subst_lcomp :
  FStar_Syntax_Syntax.subst_t ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun subst1  ->
    fun lc  ->
      let uu____4285 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4285
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4288  ->
           let uu____4289 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4289)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4295 =
      let uu____4296 = FStar_Syntax_Subst.compress t  in
      uu____4296.FStar_Syntax_Syntax.n  in
    match uu____4295 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4299 -> true
    | uu____4312 -> false
  
let (label :
  Prims.string ->
    FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun reason  ->
    fun r  ->
      fun f  ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             (f, (FStar_Syntax_Syntax.Meta_labeled (reason, r, false))))
          FStar_Pervasives_Native.None f.FStar_Syntax_Syntax.pos
  
let (label_opt :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Range.range -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun reason  ->
      fun r  ->
        fun f  ->
          match reason with
          | FStar_Pervasives_Native.None  -> f
          | FStar_Pervasives_Native.Some reason1 ->
              let uu____4369 =
                let uu____4370 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4370  in
              if uu____4369
              then f
              else (let uu____4372 = reason1 ()  in label uu____4372 r f)
  
let (label_guard :
  FStar_Range.range ->
    Prims.string ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun r  ->
    fun reason  ->
      fun g  ->
        match g.FStar_TypeChecker_Env.guard_f with
        | FStar_TypeChecker_Common.Trivial  -> g
        | FStar_TypeChecker_Common.NonTrivial f ->
            let uu___132_4389 = g  in
            let uu____4390 =
              let uu____4391 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4391  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4390;
              FStar_TypeChecker_Env.deferred =
                (uu___132_4389.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_4389.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_4389.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4411 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4411
        then c
        else
          (let uu____4413 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4413
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4472 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4472]  in
                       let us =
                         let uu____4488 =
                           let uu____4491 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4491]  in
                         u_res :: uu____4488  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4497 =
                         let uu____4502 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4503 =
                           let uu____4504 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4511 =
                             let uu____4520 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4527 =
                               let uu____4536 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4536]  in
                             uu____4520 :: uu____4527  in
                           uu____4504 :: uu____4511  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4502 uu____4503
                          in
                       uu____4497 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4570 = destruct_comp c1  in
              match uu____4570 with
              | (u_res_t,res_t,wp) ->
                  let md =
                    FStar_TypeChecker_Env.get_effect_decl env
                      c1.FStar_Syntax_Syntax.effect_name
                     in
                  let wp1 = close_wp u_res_t md res_t bvs wp  in
                  mk_comp md u_res_t c1.FStar_Syntax_Syntax.result_typ wp1
                    c1.FStar_Syntax_Syntax.flags))
  
let (close_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun bvs  ->
      fun lc  ->
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
          (fun uu____4605  ->
             let uu____4606 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4606)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___104_4615  ->
            match uu___104_4615 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4616 -> false))
  
let (should_return :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp -> Prims.bool)
  =
  fun env  ->
    fun eopt  ->
      fun lc  ->
        match eopt with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some e ->
            (((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc) &&
                (let uu____4638 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4638))
               &&
               (let uu____4645 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4645 with
                | (head1,uu____4659) ->
                    let uu____4676 =
                      let uu____4677 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4677.FStar_Syntax_Syntax.n  in
                    (match uu____4676 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4681 =
                           let uu____4682 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4682
                            in
                         Prims.op_Negation uu____4681
                     | uu____4683 -> true)))
              &&
              (let uu____4685 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4685)
  
let (return_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun u_t_opt  ->
      fun t  ->
        fun v1  ->
          let c =
            let uu____4719 =
              let uu____4720 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4720  in
            if uu____4719
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4722 = FStar_Syntax_Util.is_unit t  in
               if uu____4722
               then
                 FStar_Syntax_Syntax.mk_Total' t
                   (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.U_zero)
               else
                 (let m =
                    FStar_TypeChecker_Env.get_effect_decl env
                      FStar_Parser_Const.effect_PURE_lid
                     in
                  let u_t =
                    match u_t_opt with
                    | FStar_Pervasives_Native.None  ->
                        env.FStar_TypeChecker_Env.universe_of env t
                    | FStar_Pervasives_Native.Some u_t -> u_t  in
                  let wp =
                    let uu____4728 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4728
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4730 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4730 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4740 =
                             let uu____4741 =
                               let uu____4746 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4747 =
                                 let uu____4748 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4755 =
                                   let uu____4764 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4764]  in
                                 uu____4748 :: uu____4755  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4746
                                 uu____4747
                                in
                             uu____4741 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4740)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4792 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4792
           then
             let uu____4793 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4794 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4795 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4793 uu____4794 uu____4795
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4808 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___105_4812  ->
              match uu___105_4812 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4813 -> false))
       in
    if uu____4808
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___106_4822  ->
              match uu___106_4822 with
              | FStar_Syntax_Syntax.TOTAL  ->
                  [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | FStar_Syntax_Syntax.RETURN  ->
                  [FStar_Syntax_Syntax.PARTIAL_RETURN;
                  FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
              | f -> [f]))
  
let (weaken_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      fun formula  ->
        let uu____4841 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4841
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4844 = destruct_comp c1  in
           match uu____4844 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4858 =
                   let uu____4863 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4864 =
                     let uu____4865 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4872 =
                       let uu____4881 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4888 =
                         let uu____4897 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4897]  in
                       uu____4881 :: uu____4888  in
                     uu____4865 :: uu____4872  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4863 uu____4864  in
                 uu____4858 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4930 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4930)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4953 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4955 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4955
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4958 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4958 weaken
  
let (strengthen_comp :
  FStar_TypeChecker_Env.env ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.formula ->
          FStar_Syntax_Syntax.cflags Prims.list -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun reason  ->
      fun c  ->
        fun f  ->
          fun flags1  ->
            if env.FStar_TypeChecker_Env.lax
            then c
            else
              (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
               let uu____5001 = destruct_comp c1  in
               match uu____5001 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5015 =
                       let uu____5020 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5021 =
                         let uu____5022 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5029 =
                           let uu____5038 =
                             let uu____5045 =
                               let uu____5046 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5046 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5045
                              in
                           let uu____5053 =
                             let uu____5062 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5062]  in
                           uu____5038 :: uu____5053  in
                         uu____5022 :: uu____5029  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5020 uu____5021
                        in
                     uu____5015 FStar_Pervasives_Native.None
                       wp.FStar_Syntax_Syntax.pos
                      in
                   mk_comp md u_res_t res_t wp1 flags1)
  
let (strengthen_precondition :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_TypeChecker_Env.guard_t ->
            (FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun reason  ->
    fun env  ->
      fun e_for_debug_only  ->
        fun lc  ->
          fun g0  ->
            let uu____5137 = FStar_TypeChecker_Rel.is_trivial g0  in
            if uu____5137
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5146 =
                   let uu____5153 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5153
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5146 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5173 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___107_5181  ->
                               match uu___107_5181 with
                               | FStar_Syntax_Syntax.RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                               | FStar_Syntax_Syntax.SOMETRIVIAL  when
                                   Prims.op_Negation maybe_trivial_post ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION 
                                   when Prims.op_Negation maybe_trivial_post
                                   ->
                                   [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                               | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                   [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                               | uu____5184 -> []))
                        in
                     FStar_List.append flags1 uu____5173
                  in
               let strengthen uu____5190 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5194 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5194 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5197 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5197
                          then
                            let uu____5198 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5199 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5198 uu____5199
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5201 =
                 let uu____5202 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5202
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5201,
                 (let uu___133_5204 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___133_5204.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___133_5204.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___133_5204.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___108_5211  ->
            match uu___108_5211 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5212 -> false) lc.FStar_Syntax_Syntax.cflags)
  
let (maybe_add_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun env  ->
    fun uopt  ->
      fun lc  ->
        fun e  ->
          let uu____5239 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5239
          then e
          else
            (let uu____5243 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5245 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5245)
                in
             if uu____5243
             then
               let u =
                 match uopt with
                 | FStar_Pervasives_Native.Some u -> u
                 | FStar_Pervasives_Native.None  ->
                     env.FStar_TypeChecker_Env.universe_of env
                       lc.FStar_Syntax_Syntax.res_typ
                  in
               FStar_Syntax_Util.mk_with_type u
                 lc.FStar_Syntax_Syntax.res_typ e
             else e)
  
let (bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r1  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun uu____5295  ->
            match uu____5295 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5315 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5315 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5323 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5323
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5330 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5330
                       then
                         let uu____5333 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5333
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5337 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5337
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5342 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5342
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5346 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5346
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5355 =
                  let uu____5356 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5356
                  then
                    let u_t =
                      env.FStar_TypeChecker_Env.universe_of env
                        lc21.FStar_Syntax_Syntax.res_typ
                       in
                    lax_mk_tot_or_comp_l joined_eff u_t
                      lc21.FStar_Syntax_Syntax.res_typ []
                  else
                    (let c1 = FStar_Syntax_Syntax.lcomp_comp lc11  in
                     let c2 = FStar_Syntax_Syntax.lcomp_comp lc21  in
                     debug1
                       (fun uu____5370  ->
                          let uu____5371 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5372 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5374 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5371 uu____5372 uu____5374);
                     (let aux uu____5388 =
                        let uu____5389 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5389
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5410 ->
                              let uu____5411 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5411
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5430 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5430
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5501 =
                              let uu____5506 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5506, reason)  in
                            FStar_Util.Inl uu____5501
                        | uu____5513 -> aux ()  in
                      let try_simplify uu____5537 =
                        let rec maybe_close t x c =
                          let uu____5554 =
                            let uu____5555 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5555.FStar_Syntax_Syntax.n  in
                          match uu____5554 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5559) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5565 -> c  in
                        let uu____5566 =
                          let uu____5567 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5567  in
                        if uu____5566
                        then
                          let uu____5578 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____5578
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5592 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5592))
                        else
                          (let uu____5602 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5602
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5612 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5612
                              then
                                let uu____5621 =
                                  let uu____5626 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5626, "both gtot")  in
                                FStar_Util.Inl uu____5621
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5650 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5652 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____5652)
                                        in
                                     if uu____5650
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___134_5665 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___134_5665.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___134_5665.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____5666 =
                                         let uu____5671 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____5671, "c1 Tot")  in
                                       FStar_Util.Inl uu____5666
                                     else aux ()
                                 | uu____5677 -> aux ())))
                         in
                      let uu____5686 = try_simplify ()  in
                      match uu____5686 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5706  ->
                                let uu____5707 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5707);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5716  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5737 = lift_and_destruct env c11 c21
                                 in
                              match uu____5737 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5790 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5790]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5804 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5804]
                                     in
                                  let mk_lam wp =
                                    FStar_Syntax_Util.abs bs wp
                                      (FStar_Pervasives_Native.Some
                                         (FStar_Syntax_Util.mk_residual_comp
                                            FStar_Parser_Const.effect_Tot_lid
                                            FStar_Pervasives_Native.None
                                            [FStar_Syntax_Syntax.TOTAL]))
                                     in
                                  let r11 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_constant
                                         (FStar_Const.Const_range r1))
                                      FStar_Pervasives_Native.None r1
                                     in
                                  let wp_args =
                                    let uu____5831 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5838 =
                                      let uu____5847 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5854 =
                                        let uu____5863 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5870 =
                                          let uu____5879 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5886 =
                                            let uu____5895 =
                                              let uu____5902 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5902
                                               in
                                            [uu____5895]  in
                                          uu____5879 :: uu____5886  in
                                        uu____5863 :: uu____5870  in
                                      uu____5847 :: uu____5854  in
                                    uu____5831 :: uu____5838  in
                                  let wp =
                                    let uu____5942 =
                                      let uu____5947 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5947 wp_args
                                       in
                                    uu____5942 FStar_Pervasives_Native.None
                                      t2.FStar_Syntax_Syntax.pos
                                     in
                                  mk_comp md u_t2 t2 wp bind_flags
                               in
                            let mk_seq c11 b1 c21 =
                              let c12 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c11
                                 in
                              let c22 =
                                FStar_TypeChecker_Env.unfold_effect_abbrev
                                  env c21
                                 in
                              let uu____5972 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5972 with
                              | (m,uu____5980,lift2) ->
                                  let c23 =
                                    let uu____5983 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5983
                                     in
                                  let uu____5984 = destruct_comp c12  in
                                  (match uu____5984 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____5998 =
                                           let uu____6003 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6004 =
                                             let uu____6005 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6012 =
                                               let uu____6021 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6021]  in
                                             uu____6005 :: uu____6012  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6003 uu____6004
                                            in
                                         uu____5998
                                           FStar_Pervasives_Native.None r1
                                          in
                                       strengthen_comp env
                                         FStar_Pervasives_Native.None c23 vc1
                                         bind_flags)
                               in
                            let c1_typ =
                              FStar_TypeChecker_Env.unfold_effect_abbrev env
                                c1
                               in
                            let uu____6052 = destruct_comp c1_typ  in
                            match uu____6052 with
                            | (u_res_t1,res_t1,uu____6061) ->
                                let uu____6062 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6062
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6065 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6065
                                   then
                                     (debug1
                                        (fun uu____6073  ->
                                           let uu____6074 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6075 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6074 uu____6075);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6080 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6082 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6082)
                                         in
                                      if uu____6080
                                      then
                                        let e1' =
                                          let uu____6102 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6102
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6111  ->
                                              let uu____6112 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6113 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6112 uu____6113);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6125  ->
                                              let uu____6126 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6127 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6126 uu____6127);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6132 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6132
                                             in
                                          let c22 =
                                            weaken_comp env c21 x_eq_e  in
                                          mk_bind c1 b c22))))
                                else mk_bind c1 b c2))))
                   in
                FStar_Syntax_Syntax.mk_lcomp joined_eff
                  lc21.FStar_Syntax_Syntax.res_typ bind_flags bind_it
  
let (weaken_guard :
  FStar_TypeChecker_Common.guard_formula ->
    FStar_TypeChecker_Common.guard_formula ->
      FStar_TypeChecker_Common.guard_formula)
  =
  fun g1  ->
    fun g2  ->
      match (g1, g2) with
      | (FStar_TypeChecker_Common.NonTrivial
         f1,FStar_TypeChecker_Common.NonTrivial f2) ->
          let g = FStar_Syntax_Util.mk_imp f1 f2  in
          FStar_TypeChecker_Common.NonTrivial g
      | uu____6148 -> g2
  
let (maybe_assume_result_eq_pure_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let should_return1 =
          (((Prims.op_Negation env.FStar_TypeChecker_Env.lax) &&
              (FStar_TypeChecker_Env.lid_exists env
                 FStar_Parser_Const.effect_GTot_lid))
             && (should_return env (FStar_Pervasives_Native.Some e) lc))
            &&
            (let uu____6170 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6170)
           in
        let flags1 =
          if should_return1
          then
            let uu____6176 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6176
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6188 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6192 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6192
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6196 =
              let uu____6197 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6197  in
            (if uu____6196
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___135_6202 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___135_6202.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___135_6202.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___135_6202.FStar_Syntax_Syntax.effect_args);
                   FStar_Syntax_Syntax.flags = flags1
                 }  in
               FStar_Syntax_Syntax.mk_Comp retc2
             else FStar_Syntax_Util.comp_set_flags retc flags1)
          else
            (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
             let t = c1.FStar_Syntax_Syntax.result_typ  in
             let c2 = FStar_Syntax_Syntax.mk_Comp c1  in
             let x =
               FStar_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos)) t
                in
             let xexp = FStar_Syntax_Syntax.bv_to_name x  in
             let ret1 =
               let uu____6213 =
                 let uu____6214 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6214
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6213
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6217 =
               let uu____6218 =
                 let uu____6219 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6219
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6218  in
             FStar_Syntax_Util.comp_set_flags uu____6217 flags1)
           in
        if Prims.op_Negation should_return1
        then lc
        else
          FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
            lc.FStar_Syntax_Syntax.res_typ flags1 refine1
  
let (maybe_return_e2_and_bind :
  FStar_Range.range ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.lcomp ->
          FStar_Syntax_Syntax.term ->
            lcomp_with_binder -> FStar_Syntax_Syntax.lcomp)
  =
  fun r  ->
    fun env  ->
      fun e1opt  ->
        fun lc1  ->
          fun e2  ->
            fun uu____6254  ->
              match uu____6254 with
              | (x,lc2) ->
                  let lc21 =
                    let eff1 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc1.FStar_Syntax_Syntax.eff_name
                       in
                    let eff2 =
                      FStar_TypeChecker_Env.norm_eff_name env
                        lc2.FStar_Syntax_Syntax.eff_name
                       in
                    let uu____6266 =
                      ((let uu____6269 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6269) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6266
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6283 =
        let uu____6284 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6284  in
      FStar_Syntax_Syntax.fvar uu____6283 FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (bind_cases :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.typ,FStar_Ident.lident,FStar_Syntax_Syntax.cflags
                                                    Prims.list,Prims.bool ->
                                                                 FStar_Syntax_Syntax.lcomp)
        FStar_Pervasives_Native.tuple4 Prims.list ->
        FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun res_t  ->
      fun lcases  ->
        let eff =
          FStar_List.fold_left
            (fun eff  ->
               fun uu____6350  ->
                 match uu____6350 with
                 | (uu____6363,eff_label,uu____6365,uu____6366) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6377 =
          let uu____6384 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6418  ->
                    match uu____6418 with
                    | (uu____6431,uu____6432,flags1,uu____6434) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___109_6448  ->
                                match uu___109_6448 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6449 -> false))))
             in
          if uu____6384
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6377 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6472 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6474 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6474
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6512 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6513 =
                     let uu____6518 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6519 =
                       let uu____6520 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6527 =
                         let uu____6536 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6543 =
                           let uu____6552 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6559 =
                             let uu____6568 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6568]  in
                           uu____6552 :: uu____6559  in
                         uu____6536 :: uu____6543  in
                       uu____6520 :: uu____6527  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6518 uu____6519  in
                   uu____6513 FStar_Pervasives_Native.None uu____6512  in
                 let default_case =
                   let post_k =
                     let uu____6611 =
                       let uu____6618 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6618]  in
                     let uu____6631 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6611 uu____6631  in
                   let kwp =
                     let uu____6637 =
                       let uu____6644 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6644]  in
                     let uu____6657 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6637 uu____6657  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6664 =
                       let uu____6665 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6665]  in
                     let uu____6678 =
                       let uu____6681 =
                         let uu____6688 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6688
                          in
                       let uu____6689 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6681 uu____6689  in
                     FStar_Syntax_Util.abs uu____6664 uu____6678
                       (FStar_Pervasives_Native.Some
                          (FStar_Syntax_Util.mk_residual_comp
                             FStar_Parser_Const.effect_Tot_lid
                             FStar_Pervasives_Native.None
                             [FStar_Syntax_Syntax.TOTAL]))
                      in
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       FStar_Parser_Const.effect_PURE_lid
                      in
                   mk_comp md u_res_t res_t wp []  in
                 let maybe_return eff_label_then cthen =
                   let uu____6711 =
                     should_not_inline_whole_match ||
                       (let uu____6713 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6713)
                      in
                   if uu____6711 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6746  ->
                        fun celse  ->
                          match uu____6746 with
                          | (g,eff_label,uu____6762,cthen) ->
                              let uu____6774 =
                                let uu____6799 =
                                  let uu____6800 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6800
                                   in
                                lift_and_destruct env uu____6799 celse  in
                              (match uu____6774 with
                               | ((md,uu____6802,uu____6803),(uu____6804,uu____6805,wp_then),
                                  (uu____6807,uu____6808,wp_else)) ->
                                   let uu____6828 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6828 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6842::[] -> comp
                 | uu____6882 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6900 = destruct_comp comp1  in
                     (match uu____6900 with
                      | (uu____6907,uu____6908,wp) ->
                          let wp1 =
                            let uu____6913 =
                              let uu____6918 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6919 =
                                let uu____6920 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6927 =
                                  let uu____6936 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6936]  in
                                uu____6920 :: uu____6927  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6918
                                uu____6919
                               in
                            uu____6913 FStar_Pervasives_Native.None
                              wp.FStar_Syntax_Syntax.pos
                             in
                          mk_comp md u_res_t res_t wp1 bind_cases_flags))
               in
            FStar_Syntax_Syntax.mk_lcomp eff res_t bind_cases_flags
              bind_cases
  
let (check_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_Syntax_Syntax.comp ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun c'  ->
          let uu____6995 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____6995 with
          | FStar_Pervasives_Native.None  ->
              let uu____7004 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7009 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7004 uu____7009
          | FStar_Pervasives_Native.Some g -> (e, c', g)
  
let (maybe_coerce_bool_to_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let is_type1 t1 =
            let t2 = FStar_TypeChecker_Normalize.unfold_whnf env t1  in
            let uu____7052 =
              let uu____7053 = FStar_Syntax_Subst.compress t2  in
              uu____7053.FStar_Syntax_Syntax.n  in
            match uu____7052 with
            | FStar_Syntax_Syntax.Tm_type uu____7056 -> true
            | uu____7057 -> false  in
          let uu____7058 =
            let uu____7059 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7059.FStar_Syntax_Syntax.n  in
          match uu____7058 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7067 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7077 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7077
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7079 =
                  let uu____7080 =
                    let uu____7081 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7081
                     in
                  (FStar_Pervasives_Native.None, uu____7080)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7079
                 in
              let e1 =
                let uu____7087 =
                  let uu____7092 =
                    let uu____7093 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7093]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7092  in
                uu____7087 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7114 -> (e, lc)
  
let (weaken_result_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.lcomp ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.lcomp,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        fun t  ->
          let use_eq =
            env.FStar_TypeChecker_Env.use_eq ||
              (let uu____7151 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7151 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7174 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7196 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7196, false)
            else
              (let uu____7202 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7202, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7213) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7222 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7222 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___136_7236 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___136_7236.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___136_7236.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___136_7236.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7241 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7241 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___137_7249 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___137_7249.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___137_7249.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___137_7249.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___138_7252 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___138_7252.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___138_7252.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___138_7252.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7258 =
                     let uu____7259 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7259
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7262 =
                          let uu____7263 = FStar_Syntax_Subst.compress f1  in
                          uu____7263.FStar_Syntax_Syntax.n  in
                        match uu____7262 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7266,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7268;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7269;_},uu____7270)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___139_7292 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___139_7292.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___139_7292.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___139_7292.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7293 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7296 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7296
                              then
                                let uu____7297 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7298 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7299 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7300 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7297 uu____7298 uu____7299 uu____7300
                              else ());
                             (let u_t_opt = comp_univ_opt c  in
                              let x =
                                FStar_Syntax_Syntax.new_bv
                                  (FStar_Pervasives_Native.Some
                                     (t.FStar_Syntax_Syntax.pos)) t
                                 in
                              let xexp = FStar_Syntax_Syntax.bv_to_name x  in
                              let cret = return_value env u_t_opt t xexp  in
                              let guard =
                                if apply_guard1
                                then
                                  let uu____7309 =
                                    let uu____7314 =
                                      let uu____7315 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7315]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7314
                                     in
                                  uu____7309 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7337 =
                                let uu____7342 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7359 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7360 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7361 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7342 uu____7359
                                  e uu____7360 uu____7361
                                 in
                              match uu____7337 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___140_7365 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___140_7365.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___140_7365.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7367 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7367
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7372 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7372
                                    then
                                      let uu____7373 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7373
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___110_7383  ->
                             match uu___110_7383 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7386 -> []))
                      in
                   let lc1 =
                     let uu____7388 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7388 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___141_7390 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_7390.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_7390.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_7390.FStar_TypeChecker_Env.implicits)
                     }  in
                   (e, lc1, g2))
  
let (pure_or_ghost_pre_and_post :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun comp  ->
      let mk_post_type res_t ens =
        let x = FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t
           in
        let uu____7425 =
          let uu____7428 =
            let uu____7433 =
              let uu____7434 =
                let uu____7441 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7441  in
              [uu____7434]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7433  in
          uu____7428 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7425  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7462 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7462
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7478 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7493 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7509 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7509
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7523)::(ens,uu____7525)::uu____7526 ->
                    let uu____7555 =
                      let uu____7558 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7558  in
                    let uu____7559 =
                      let uu____7560 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7560  in
                    (uu____7555, uu____7559)
                | uu____7563 ->
                    let uu____7572 =
                      let uu____7577 =
                        let uu____7578 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7578
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7577)
                       in
                    FStar_Errors.raise_error uu____7572
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7594)::uu____7595 ->
                    let uu____7614 =
                      let uu____7619 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7619
                       in
                    (match uu____7614 with
                     | (us_r,uu____7651) ->
                         let uu____7652 =
                           let uu____7657 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7657
                            in
                         (match uu____7652 with
                          | (us_e,uu____7689) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____7692 =
                                  let uu____7693 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7693
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7692
                                  us_r
                                 in
                              let as_ens =
                                let uu____7695 =
                                  let uu____7696 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7696
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7695
                                  us_e
                                 in
                              let req =
                                let uu____7700 =
                                  let uu____7705 =
                                    let uu____7706 =
                                      let uu____7715 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7715]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7706
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7705
                                   in
                                uu____7700 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____7747 =
                                  let uu____7752 =
                                    let uu____7753 =
                                      let uu____7762 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7762]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7753
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7752
                                   in
                                uu____7747 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____7791 =
                                let uu____7794 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____7794  in
                              let uu____7795 =
                                let uu____7796 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____7796  in
                              (uu____7791, uu____7795)))
                | uu____7799 -> failwith "Impossible"))
  
let (reify_body :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t  in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
         in
      (let uu____7829 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____7829
       then
         let uu____7830 = FStar_Syntax_Print.term_to_string tm  in
         let uu____7831 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7830 uu____7831
       else ());
      tm'
  
let (reify_body_with_arg :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun head1  ->
      fun arg  ->
        let tm =
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (head1, [arg]))
            FStar_Pervasives_Native.None head1.FStar_Syntax_Syntax.pos
           in
        let tm' =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.Reify;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.EraseUniverses;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm
           in
        (let uu____7875 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____7875
         then
           let uu____7876 = FStar_Syntax_Print.term_to_string tm  in
           let uu____7877 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7876
             uu____7877
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____7884 =
      let uu____7885 =
        let uu____7886 = FStar_Syntax_Subst.compress t  in
        uu____7886.FStar_Syntax_Syntax.n  in
      match uu____7885 with
      | FStar_Syntax_Syntax.Tm_app uu____7889 -> false
      | uu____7904 -> true  in
    if uu____7884
    then t
    else
      (let uu____7906 = FStar_Syntax_Util.head_and_args t  in
       match uu____7906 with
       | (head1,args) ->
           let uu____7943 =
             let uu____7944 =
               let uu____7945 = FStar_Syntax_Subst.compress head1  in
               uu____7945.FStar_Syntax_Syntax.n  in
             match uu____7944 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7948 -> false  in
           if uu____7943
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7970 ->
                  failwith
                    "Impossible : Reify applied to multiple arguments after normalization.")
           else t)
  
let (maybe_instantiate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.typ,FStar_TypeChecker_Env.guard_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let torig = FStar_Syntax_Subst.compress t  in
        if Prims.op_Negation env.FStar_TypeChecker_Env.instantiate_imp
        then (e, torig, FStar_TypeChecker_Rel.trivial_guard)
        else
          (let number_of_implicits t1 =
             let uu____8015 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8015 with
             | (formals,uu____8029) ->
                 let n_implicits =
                   let uu____8047 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8125  ->
                             match uu____8125 with
                             | (uu____8132,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8047 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8265 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8265 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8289 =
                     let uu____8294 =
                       let uu____8295 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8302 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8303 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8295 uu____8302 uu____8303
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8294)
                      in
                   let uu____8310 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8289 uu____8310
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___111_8333 =
             match uu___111_8333 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8363 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8363 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8478) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8521,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8554 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8554 with
                           | (v1,uu____8594,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____8613 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____8613 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8706 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8706)))
                      | (uu____8733,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____8779 =
                      let uu____8806 = inst_n_binders t  in
                      aux [] uu____8806 bs1  in
                    (match uu____8779 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8877) -> (e, torig, guard)
                          | (uu____8908,[]) when
                              let uu____8939 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8939 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8940 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8968 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8981 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____8991 =
      let uu____8994 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____8994
        (FStar_List.map
           (fun u  ->
              let uu____9004 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9004 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____8991 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9025 = FStar_Util.set_is_empty x  in
      if uu____9025
      then []
      else
        (let s =
           let uu____9040 =
             let uu____9043 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9043  in
           FStar_All.pipe_right uu____9040 FStar_Util.set_elements  in
         (let uu____9059 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9059
          then
            let uu____9060 =
              let uu____9061 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9061  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9060
          else ());
         (let r =
            let uu____9068 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9068  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9107 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9107
                     then
                       let uu____9108 =
                         let uu____9109 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9109
                          in
                       let uu____9110 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9111 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9108 uu____9110 uu____9111
                     else ());
                    FStar_Syntax_Unionfind.univ_change u
                      (FStar_Syntax_Syntax.U_name u_name);
                    u_name))
             in
          u_names))
  
let (gather_free_univnames :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun t  ->
      let ctx_univnames = FStar_TypeChecker_Env.univnames env  in
      let tm_univnames = FStar_Syntax_Free.univnames t  in
      let univnames1 =
        let uu____9137 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9137 FStar_Util.set_elements  in
      univnames1
  
let (check_universe_generalization :
  FStar_Syntax_Syntax.univ_name Prims.list ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun explicit_univ_names  ->
    fun generalized_univ_names  ->
      fun t  ->
        match (explicit_univ_names, generalized_univ_names) with
        | ([],uu____9175) -> generalized_univ_names
        | (uu____9182,[]) -> explicit_univ_names
        | uu____9189 ->
            let uu____9198 =
              let uu____9203 =
                let uu____9204 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9204
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9203)
               in
            FStar_Errors.raise_error uu____9198 t.FStar_Syntax_Syntax.pos
  
let (generalize_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t0  ->
      let t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.NoFullNorm;
          FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env t0
         in
      let univnames1 = gather_free_univnames env t  in
      (let uu____9222 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9222
       then
         let uu____9223 = FStar_Syntax_Print.term_to_string t  in
         let uu____9224 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9223 uu____9224
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9230 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9230
        then
          let uu____9231 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9231
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9237 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9237
         then
           let uu____9238 = FStar_Syntax_Print.term_to_string t  in
           let uu____9239 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9238 uu____9239
         else ());
        (let univs2 = check_universe_generalization univnames1 gen1 t0  in
         let t1 = FStar_TypeChecker_Normalize.reduce_uvar_solutions env t  in
         let ts = FStar_Syntax_Subst.close_univ_vars univs2 t1  in
         (univs2, ts))))
  
let (gen :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_name Prims.list,
          FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder
                                                              Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        let uu____9317 =
          let uu____9318 =
            FStar_Util.for_all
              (fun uu____9331  ->
                 match uu____9331 with
                 | (uu____9340,uu____9341,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9318  in
        if uu____9317
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9389 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9389
              then
                let uu____9390 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9390
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9394 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9394
               then
                 let uu____9395 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9395
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9410 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9410 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9446 =
             match uu____9446 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9490 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9490
                   then
                     let uu____9491 =
                       let uu____9492 =
                         let uu____9495 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9495
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9492
                         (FStar_String.concat ", ")
                        in
                     let uu____9538 =
                       let uu____9539 =
                         let uu____9542 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9542
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9553 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9554 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9553
                                   uu____9554))
                          in
                       FStar_All.pipe_right uu____9539
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9491
                       uu____9538
                   else ());
                  (let univs2 =
                     let uu____9561 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____9573 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____9573) univs1
                       uu____9561
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____9580 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____9580
                    then
                      let uu____9581 =
                        let uu____9582 =
                          let uu____9585 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____9585
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____9582
                          (FStar_String.concat ", ")
                         in
                      let uu____9628 =
                        let uu____9629 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____9640 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____9641 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____9640
                                    uu____9641))
                           in
                        FStar_All.pipe_right uu____9629
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9581
                        uu____9628
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____9655 =
             let uu____9672 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____9672  in
           match uu____9655 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9764 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9764
                 then ()
                 else
                   (let uu____9766 = lec_hd  in
                    match uu____9766 with
                    | (lb1,uu____9774,uu____9775) ->
                        let uu____9776 = lec2  in
                        (match uu____9776 with
                         | (lb2,uu____9784,uu____9785) ->
                             let msg =
                               let uu____9787 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9788 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9787 uu____9788
                                in
                             let uu____9789 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9789))
                  in
               let force_uvars_eq lec2 u1 u2 =
                 let uvars_subseteq u11 u21 =
                   FStar_All.pipe_right u11
                     (FStar_Util.for_all
                        (fun u  ->
                           FStar_All.pipe_right u21
                             (FStar_Util.for_some
                                (fun u'  ->
                                   FStar_Syntax_Unionfind.equiv
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                     u'.FStar_Syntax_Syntax.ctx_uvar_head))))
                    in
                 let uu____9853 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9853
                 then ()
                 else
                   (let uu____9855 = lec_hd  in
                    match uu____9855 with
                    | (lb1,uu____9863,uu____9864) ->
                        let uu____9865 = lec2  in
                        (match uu____9865 with
                         | (lb2,uu____9873,uu____9874) ->
                             let msg =
                               let uu____9876 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9877 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9876 uu____9877
                                in
                             let uu____9878 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9878))
                  in
               let lecs1 =
                 let uu____9888 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9947 = univs_and_uvars_of_lec this_lec  in
                        match uu____9947 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9888 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10048 = lec_hd  in
                   match uu____10048 with
                   | (lbname,e,c) ->
                       let uu____10058 =
                         let uu____10063 =
                           let uu____10064 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10065 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10066 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10064 uu____10065 uu____10066
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10063)
                          in
                       let uu____10067 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10058 uu____10067
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10088 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10088 with
                         | FStar_Pervasives_Native.Some uu____10097 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10104 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10108 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10108 with
                              | (bs,kres) ->
                                  ((let uu____10146 =
                                      let uu____10147 =
                                        let uu____10150 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10150
                                         in
                                      uu____10147.FStar_Syntax_Syntax.n  in
                                    match uu____10146 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10151
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10155 =
                                          let uu____10156 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10156  in
                                        if uu____10155
                                        then fail1 kres
                                        else ()
                                    | uu____10158 -> fail1 kres);
                                   (let a =
                                      let uu____10160 =
                                        let uu____10163 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10163
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10160
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10171 ->
                                          let uu____10178 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10178
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_tot
                                                  kres))
                                       in
                                    FStar_Syntax_Util.set_uvar
                                      u.FStar_Syntax_Syntax.ctx_uvar_head t;
                                    (a,
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag)))))))
                  in
               let gen_univs1 = gen_univs env univs1  in
               let gen_tvars = gen_types uvs  in
               let ecs =
                 FStar_All.pipe_right lecs2
                   (FStar_List.map
                      (fun uu____10289  ->
                         match uu____10289 with
                         | (lbname,e,c) ->
                             let uu____10343 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10418 ->
                                   let uu____10433 = (e, c)  in
                                   (match uu____10433 with
                                    | (e0,c0) ->
                                        let c1 =
                                          FStar_TypeChecker_Normalize.normalize_comp
                                            [FStar_TypeChecker_Normalize.Beta;
                                            FStar_TypeChecker_Normalize.DoNotUnfoldPureLets;
                                            FStar_TypeChecker_Normalize.CompressUvars;
                                            FStar_TypeChecker_Normalize.NoFullNorm;
                                            FStar_TypeChecker_Normalize.Exclude
                                              FStar_TypeChecker_Normalize.Zeta]
                                            env c
                                           in
                                        let e1 =
                                          FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                            env e
                                           in
                                        let e2 =
                                          if is_rec
                                          then
                                            let tvar_args =
                                              FStar_List.map
                                                (fun uu____10484  ->
                                                   match uu____10484 with
                                                   | (x,uu____10492) ->
                                                       let uu____10497 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10497)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10515 =
                                                let uu____10516 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10516
                                                 in
                                              if uu____10515
                                              then
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  tm tvar_args
                                                  FStar_Pervasives_Native.None
                                                  tm.FStar_Syntax_Syntax.pos
                                              else tm  in
                                            FStar_Syntax_InstFV.inst
                                              instantiate_lbname_with_app e1
                                          else e1  in
                                        let t =
                                          let uu____10522 =
                                            let uu____10523 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10523.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10522 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10544 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10544 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10557 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10561 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10561, gen_tvars))
                                in
                             (match uu____10343 with
                              | (e1,c1,gvs) ->
                                  (lbname, gen_univs1, e1, c1, gvs))))
                  in
               FStar_Pervasives_Native.Some ecs)
  
let (generalize :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.comp)
        FStar_Pervasives_Native.tuple3 Prims.list ->
        (FStar_Syntax_Syntax.lbname,FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.term,
          FStar_Syntax_Syntax.comp,FStar_Syntax_Syntax.binder Prims.list)
          FStar_Pervasives_Native.tuple5 Prims.list)
  =
  fun env  ->
    fun is_rec  ->
      fun lecs  ->
        (let uu____10715 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10715
         then
           let uu____10716 =
             let uu____10717 =
               FStar_List.map
                 (fun uu____10730  ->
                    match uu____10730 with
                    | (lb,uu____10738,uu____10739) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10717 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10716
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10760  ->
                match uu____10760 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10789 = gen env is_rec lecs  in
           match uu____10789 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10888  ->
                       match uu____10888 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10950 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10950
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____10996  ->
                           match uu____10996 with
                           | (l,us,e,c,gvs) ->
                               let uu____11030 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11031 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11032 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11033 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11034 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11030 uu____11031 uu____11032
                                 uu____11033 uu____11034))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11075  ->
                match uu____11075 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11119 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11119, t, c, gvs)) univnames_lecs
           generalized_lecs)
  
let (check_and_ascribe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let env1 =
            FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
          let check1 env2 t11 t21 =
            if env2.FStar_TypeChecker_Env.use_eq
            then FStar_TypeChecker_Rel.try_teq true env2 t11 t21
            else
              (let uu____11176 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11176 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11182 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11182)
             in
          let is_var e1 =
            let uu____11191 =
              let uu____11192 = FStar_Syntax_Subst.compress e1  in
              uu____11192.FStar_Syntax_Syntax.n  in
            match uu____11191 with
            | FStar_Syntax_Syntax.Tm_name uu____11195 -> true
            | uu____11196 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___142_11216 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___142_11216.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___142_11216.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11217 -> e2  in
          let env2 =
            let uu___143_11219 = env1  in
            let uu____11220 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___143_11219.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___143_11219.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___143_11219.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___143_11219.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___143_11219.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___143_11219.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___143_11219.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___143_11219.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___143_11219.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___143_11219.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___143_11219.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___143_11219.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___143_11219.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___143_11219.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___143_11219.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___143_11219.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11220;
              FStar_TypeChecker_Env.is_iface =
                (uu___143_11219.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___143_11219.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___143_11219.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___143_11219.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___143_11219.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___143_11219.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___143_11219.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___143_11219.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___143_11219.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___143_11219.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___143_11219.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___143_11219.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___143_11219.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___143_11219.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___143_11219.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___143_11219.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___143_11219.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___143_11219.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___143_11219.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___143_11219.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___143_11219.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11221 = check1 env2 t1 t2  in
          match uu____11221 with
          | FStar_Pervasives_Native.None  ->
              let uu____11228 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11233 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11228 uu____11233
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11240 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11240
                then
                  let uu____11241 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11241
                else ());
               (let uu____11243 = decorate e t2  in (uu____11243, g)))
  
let (check_top_level :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.guard_t ->
      FStar_Syntax_Syntax.lcomp ->
        (Prims.bool,FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun g  ->
      fun lc  ->
        let discharge g1 =
          FStar_TypeChecker_Rel.force_trivial_guard env g1;
          FStar_Syntax_Util.is_pure_lcomp lc  in
        let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g  in
        let uu____11275 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11275
        then
          let uu____11280 = discharge g1  in
          let uu____11281 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11280, uu____11281)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11288 =
               let uu____11289 =
                 let uu____11290 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11290 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11289
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11288
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11292 = destruct_comp c1  in
           match uu____11292 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11309 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11310 =
                   let uu____11315 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11316 =
                     let uu____11317 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11324 =
                       let uu____11333 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11333]  in
                     uu____11317 :: uu____11324  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11315 uu____11316  in
                 uu____11310 FStar_Pervasives_Native.None uu____11309  in
               ((let uu____11361 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11361
                 then
                   let uu____11362 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11362
                 else ());
                (let g2 =
                   let uu____11365 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11365  in
                 let uu____11366 = discharge g2  in
                 let uu____11367 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11366, uu____11367))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___112_11399 =
        match uu___112_11399 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11407)::[] -> f fst1
        | uu____11424 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11435 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11435
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11446 =
          let uu____11447 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11447  in
        FStar_All.pipe_right uu____11446
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11466 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11466
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___113_11480 =
        match uu___113_11480 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11488)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11507)::[] ->
            let uu____11536 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11536
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11537 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11548 =
          let uu____11556 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11556)  in
        let uu____11564 =
          let uu____11574 =
            let uu____11582 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____11582)  in
          let uu____11590 =
            let uu____11600 =
              let uu____11608 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____11608)  in
            let uu____11616 =
              let uu____11626 =
                let uu____11634 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____11634)  in
              let uu____11642 =
                let uu____11652 =
                  let uu____11660 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____11660)  in
                [uu____11652; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____11626 :: uu____11642  in
            uu____11600 :: uu____11616  in
          uu____11574 :: uu____11590  in
        uu____11548 :: uu____11564  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11722 =
            FStar_Util.find_map table
              (fun uu____11737  ->
                 match uu____11737 with
                 | (x,mk1) ->
                     let uu____11754 = FStar_Ident.lid_equals x lid  in
                     if uu____11754
                     then
                       let uu____11757 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11757
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11722 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11760 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11766 =
      let uu____11767 = FStar_Syntax_Util.un_uinst l  in
      uu____11767.FStar_Syntax_Syntax.n  in
    match uu____11766 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11771 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11801)::uu____11802 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11813 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11820,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11821))::uu____11822 -> bs
      | uu____11833 ->
          let uu____11834 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11834 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11838 =
                 let uu____11839 = FStar_Syntax_Subst.compress t  in
                 uu____11839.FStar_Syntax_Syntax.n  in
               (match uu____11838 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11843) ->
                    let uu____11860 =
                      FStar_Util.prefix_until
                        (fun uu___114_11900  ->
                           match uu___114_11900 with
                           | (uu____11907,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11908)) ->
                               false
                           | uu____11911 -> true) bs'
                       in
                    (match uu____11860 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11946,uu____11947) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12019,uu____12020) ->
                         let uu____12093 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12111  ->
                                   match uu____12111 with
                                   | (x,uu____12119) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12093
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12162  ->
                                     match uu____12162 with
                                     | (x,i) ->
                                         let uu____12181 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12181, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12189 -> bs))
  
let (maybe_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c1  ->
        fun c2  ->
          fun t  ->
            let m1 = FStar_TypeChecker_Env.norm_eff_name env c1  in
            let m2 = FStar_TypeChecker_Env.norm_eff_name env c2  in
            let uu____12217 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12217
            then e
            else
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_meta
                   (e, (FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))))
                FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (maybe_monadic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun c  ->
        fun t  ->
          let m = FStar_TypeChecker_Env.norm_eff_name env c  in
          let uu____12244 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12244
          then e
          else
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_meta
                 (e, (FStar_Syntax_Syntax.Meta_monadic (m, t))))
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (d : Prims.string -> unit) =
  fun s  -> FStar_Util.print1 "\027[01;36m%s\027[00m\n" s 
let (mk_toplevel_definition :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.sigelt,FStar_Syntax_Syntax.term)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun lident  ->
      fun def  ->
        (let uu____12279 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12279
         then
           ((let uu____12281 = FStar_Ident.text_of_lid lident  in
             d uu____12281);
            (let uu____12282 = FStar_Ident.text_of_lid lident  in
             let uu____12283 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12282 uu____12283))
         else ());
        (let fv =
           let uu____12286 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12286
             FStar_Pervasives_Native.None
            in
         let lbname = FStar_Util.Inr fv  in
         let lb =
           (false,
             [FStar_Syntax_Util.mk_letbinding lbname []
                FStar_Syntax_Syntax.tun FStar_Parser_Const.effect_Tot_lid def
                [] FStar_Range.dummyRange])
            in
         let sig_ctx =
           FStar_Syntax_Syntax.mk_sigelt
             (FStar_Syntax_Syntax.Sig_let (lb, [lident]))
            in
         let uu____12296 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___144_12298 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___144_12298.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___144_12298.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___144_12298.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___144_12298.FStar_Syntax_Syntax.sigattrs)
           }), uu____12296))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___115_12314 =
        match uu___115_12314 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12315 -> false  in
      let reducibility uu___116_12321 =
        match uu___116_12321 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12322 -> false  in
      let assumption uu___117_12328 =
        match uu___117_12328 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12329 -> false  in
      let reification uu___118_12335 =
        match uu___118_12335 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12336 -> true
        | uu____12337 -> false  in
      let inferred uu___119_12343 =
        match uu___119_12343 with
        | FStar_Syntax_Syntax.Discriminator uu____12344 -> true
        | FStar_Syntax_Syntax.Projector uu____12345 -> true
        | FStar_Syntax_Syntax.RecordType uu____12350 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12359 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12368 -> false  in
      let has_eq uu___120_12374 =
        match uu___120_12374 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12375 -> false  in
      let quals_combo_ok quals q =
        match q with
        | FStar_Syntax_Syntax.Assumption  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                          (inferred x))
                         || (visibility x))
                        || (assumption x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Inline_for_extraction)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.New  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (assumption x)))
        | FStar_Syntax_Syntax.Inline_for_extraction  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                           (visibility x))
                          || (reducibility x))
                         || (reification x))
                        || (inferred x))
                       ||
                       (env.FStar_TypeChecker_Env.is_iface &&
                          (x = FStar_Syntax_Syntax.Assumption)))
                      || (x = FStar_Syntax_Syntax.NoExtract)))
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Visible_default  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Irreducible  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Abstract  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Noeq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.Unopteq  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((((((x = q) || (x = FStar_Syntax_Syntax.Logic)) ||
                            (x = FStar_Syntax_Syntax.Abstract))
                           || (x = FStar_Syntax_Syntax.Inline_for_extraction))
                          || (x = FStar_Syntax_Syntax.NoExtract))
                         || (has_eq x))
                        || (inferred x))
                       || (visibility x))
                      || (reification x)))
        | FStar_Syntax_Syntax.TotalEffect  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    (((x = q) || (inferred x)) || (visibility x)) ||
                      (reification x)))
        | FStar_Syntax_Syntax.Logic  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((x = q) || (x = FStar_Syntax_Syntax.Assumption)) ||
                        (inferred x))
                       || (visibility x))
                      || (reducibility x)))
        | FStar_Syntax_Syntax.Reifiable  ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Reflectable uu____12439 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12444 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12448 =
        let uu____12449 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___121_12453  ->
                  match uu___121_12453 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12454 -> false))
           in
        FStar_All.pipe_right uu____12449 Prims.op_Negation  in
      if uu____12448
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12469 =
            let uu____12474 =
              let uu____12475 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12475 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12474)  in
          FStar_Errors.raise_error uu____12469 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12487 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12491 =
            let uu____12492 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12492  in
          if uu____12491 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12497),uu____12498) ->
              ((let uu____12508 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12508
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12512 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12512
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12518 ->
              let uu____12527 =
                let uu____12528 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12528  in
              if uu____12527 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12534 ->
              let uu____12541 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12541 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12545 ->
              let uu____12552 =
                let uu____12553 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12553  in
              if uu____12552 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12559 ->
              let uu____12560 =
                let uu____12561 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12561  in
              if uu____12560 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12567 ->
              let uu____12568 =
                let uu____12569 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12569  in
              if uu____12568 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12575 ->
              let uu____12588 =
                let uu____12589 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____12589  in
              if uu____12588 then err'1 () else ()
          | uu____12595 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____12629 =
          let uu____12630 = FStar_Syntax_Subst.compress t1  in
          uu____12630.FStar_Syntax_Syntax.n  in
        match uu____12629 with
        | FStar_Syntax_Syntax.Tm_type uu____12633 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____12636 =
                 let uu____12641 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____12641
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____12636
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____12659 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____12659
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____12676 =
                                 let uu____12677 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____12677.FStar_Syntax_Syntax.n  in
                               match uu____12676 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____12681 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____12682 ->
            let uu____12695 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____12695 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____12721 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____12721
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____12723;
               FStar_Syntax_Syntax.index = uu____12724;
               FStar_Syntax_Syntax.sort = t2;_},uu____12726)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12734,uu____12735) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____12777::[]) ->
            let uu____12808 =
              let uu____12809 = FStar_Syntax_Util.un_uinst head1  in
              uu____12809.FStar_Syntax_Syntax.n  in
            (match uu____12808 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____12813 -> false)
        | uu____12814 -> false
      
      and aux env t1 =
        let t2 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Normalize.Primops;
            FStar_TypeChecker_Normalize.Weak;
            FStar_TypeChecker_Normalize.HNF;
            FStar_TypeChecker_Normalize.UnfoldUntil
              FStar_Syntax_Syntax.delta_constant;
            FStar_TypeChecker_Normalize.Beta;
            FStar_TypeChecker_Normalize.AllowUnboundUniverses;
            FStar_TypeChecker_Normalize.Zeta;
            FStar_TypeChecker_Normalize.Iota] env t1
           in
        let res = aux_whnf env t2  in
        (let uu____12822 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____12822
         then
           let uu____12823 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____12823
         else ());
        res
       in aux g t
  