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
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.should_check_uvar ->
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,(FStar_Syntax_Syntax.ctx_uvar,
                                                                    FStar_Range.range)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list,
              FStar_TypeChecker_Env.guard_t) FStar_Pervasives_Native.tuple3)
  =
  fun reason  ->
    fun r  ->
      fun env  ->
        fun k  ->
          fun should_check  ->
            let uu____70 =
              FStar_Syntax_Util.destruct k FStar_Parser_Const.range_of_lid
               in
            match uu____70 with
            | FStar_Pervasives_Native.Some (uu____95::(tm,uu____97)::[]) ->
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_range (tm.FStar_Syntax_Syntax.pos)))
                    FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                   in
                (t, [], FStar_TypeChecker_Rel.trivial_guard)
            | uu____149 ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let gamma = env.FStar_TypeChecker_Env.gamma  in
                let ctx_uvar =
                  let uu____165 = FStar_Syntax_Unionfind.fresh ()  in
                  {
                    FStar_Syntax_Syntax.ctx_uvar_head = uu____165;
                    FStar_Syntax_Syntax.ctx_uvar_gamma = gamma;
                    FStar_Syntax_Syntax.ctx_uvar_binders = binders;
                    FStar_Syntax_Syntax.ctx_uvar_typ = k;
                    FStar_Syntax_Syntax.ctx_uvar_reason = reason;
                    FStar_Syntax_Syntax.ctx_uvar_should_check = should_check;
                    FStar_Syntax_Syntax.ctx_uvar_range = r
                  }  in
                (FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                   true gamma binders;
                 (let t =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_uvar
                         (ctx_uvar, ([], FStar_Pervasives_Native.None)))
                      FStar_Pervasives_Native.None r
                     in
                  let g =
                    let uu___122_199 = FStar_TypeChecker_Rel.trivial_guard
                       in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___122_199.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___122_199.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___122_199.FStar_TypeChecker_Env.univ_ineqs);
                      FStar_TypeChecker_Env.implicits =
                        [(reason, t, ctx_uvar, r)]
                    }  in
                  (t, [(ctx_uvar, r)], g)))
  
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
          new_implicit_var_aux reason r env k FStar_Syntax_Syntax.Strict
  
let (close_guard_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun xs  ->
      fun g  ->
        let uu____279 =
          FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
            (FStar_List.partition
               (fun uu____325  ->
                  match uu____325 with
                  | (uu____330,p) ->
                      FStar_TypeChecker_Rel.flex_prob_closing env xs p))
           in
        match uu____279 with
        | (solve_now,defer) ->
            ((let uu____359 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____359
              then
                (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                 FStar_List.iter
                   (fun uu____370  ->
                      match uu____370 with
                      | (s,p) ->
                          let uu____377 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____377) solve_now;
                 FStar_Util.print_string " ...DEFERRED THE REST:\n";
                 FStar_List.iter
                   (fun uu____388  ->
                      match uu____388 with
                      | (s,p) ->
                          let uu____395 =
                            FStar_TypeChecker_Rel.prob_to_string env p  in
                          FStar_Util.print2 "%s: %s\n" s uu____395) defer;
                 FStar_Util.print_string "END\n")
              else ());
             (let g1 =
                FStar_TypeChecker_Rel.solve_deferred_constraints env
                  (let uu___123_399 = g  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___123_399.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = solve_now;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___123_399.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___123_399.FStar_TypeChecker_Env.implicits)
                   })
                 in
              let g2 =
                let uu___124_401 = g1  in
                {
                  FStar_TypeChecker_Env.guard_f =
                    (uu___124_401.FStar_TypeChecker_Env.guard_f);
                  FStar_TypeChecker_Env.deferred = defer;
                  FStar_TypeChecker_Env.univ_ineqs =
                    (uu___124_401.FStar_TypeChecker_Env.univ_ineqs);
                  FStar_TypeChecker_Env.implicits =
                    (uu___124_401.FStar_TypeChecker_Env.implicits)
                }  in
              g2))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____415 =
        let uu____416 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____416  in
      if uu____415
      then
        let us =
          let uu____418 =
            let uu____421 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____421
             in
          FStar_All.pipe_right uu____418 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____432 =
            let uu____437 =
              let uu____438 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____438
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____437)  in
          FStar_Errors.log_issue r uu____432);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____455  ->
      match uu____455 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____465;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____467;
          FStar_Syntax_Syntax.lbpos = uu____468;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____501 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____501 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____538) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____545) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____600) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____632 = FStar_Options.ml_ish ()  in
                                if uu____632
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____649 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____649
                            then
                              let uu____650 = FStar_Range.string_of_range r
                                 in
                              let uu____651 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____650 uu____651
                            else ());
                           FStar_Util.Inl t2)
                      | uu____653 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____655 = aux e1  in
                      match uu____655 with
                      | FStar_Util.Inr c ->
                          let uu____661 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____661
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____663 =
                               let uu____668 =
                                 let uu____669 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____669
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____668)
                                in
                             FStar_Errors.raise_error uu____663 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____673 ->
               let uu____674 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____674 with
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
            let uu____768 =
              let uu____775 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____775 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____782;
                  FStar_Syntax_Syntax.vars = uu____783;_} ->
                  let uu____786 = FStar_Syntax_Util.type_u ()  in
                  (match uu____786 with
                   | (t,uu____798) ->
                       let uu____799 =
                         let uu____814 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var_aux "pattern bv type" uu____814
                           env1 t FStar_Syntax_Syntax.Allow_untyped
                          in
                       (match uu____799 with | (t1,uu____822,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____768 with
            | (t_x,guard) ->
                ((let uu___125_854 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___125_854.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___125_854.FStar_Syntax_Syntax.index);
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
                  | uu____929 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Rel.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____937) ->
                let uu____942 = FStar_Syntax_Util.type_u ()  in
                (match uu____942 with
                 | (k,uu____968) ->
                     let uu____969 =
                       let uu____984 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var_aux "pat_dot_term type" uu____984
                         env1 k FStar_Syntax_Syntax.Allow_untyped
                        in
                     (match uu____969 with
                      | (t,uu____1006,g) ->
                          let x1 =
                            let uu___126_1025 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___126_1025.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___126_1025.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1026 =
                            let uu____1041 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var_aux "pat_dot_term" uu____1041
                              env1 t FStar_Syntax_Syntax.Allow_untyped
                             in
                          (match uu____1026 with
                           | (e,uu____1063,g') ->
                               let p2 =
                                 let uu___127_1084 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___127_1084.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1087 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1087, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1095 = check_bv env1 x  in
                (match uu____1095 with
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
                let uu____1134 = check_bv env1 x  in
                (match uu____1134 with
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
                let uu____1189 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1323  ->
                          fun uu____1324  ->
                            match (uu____1323, uu____1324) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1522 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1522 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1598 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1598, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1189 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1729 =
                         let uu____1734 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1735 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1734 uu____1735
                          in
                       uu____1729 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1752 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1763 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1774 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1752, uu____1763, uu____1774, env2, e, guard,
                       (let uu___128_1792 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___128_1792.FStar_Syntax_Syntax.p)
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
                    (fun uu____1892  ->
                       match uu____1892 with
                       | (p2,imp) ->
                           let uu____1911 = elaborate_pat env1 p2  in
                           (uu____1911, imp)) pats
                   in
                let uu____1916 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____1916 with
                 | (uu____1923,t) ->
                     let uu____1925 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____1925 with
                      | (f,uu____1941) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2067::uu____2068) ->
                                let uu____2111 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2111
                            | (uu____2120::uu____2121,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2199  ->
                                        match uu____2199 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2226 =
                                                     let uu____2229 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2229
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2226
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2231 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2231, true)
                                             | uu____2236 ->
                                                 let uu____2239 =
                                                   let uu____2244 =
                                                     let uu____2245 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2245
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2244)
                                                    in
                                                 let uu____2246 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2239 uu____2246)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2320,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2321)) when p_imp ->
                                     let uu____2324 = aux formals' pats'  in
                                     (p2, true) :: uu____2324
                                 | (uu____2341,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2349 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2349
                                        in
                                     let uu____2350 = aux formals' pats2  in
                                     (p3, true) :: uu____2350
                                 | (uu____2367,imp) ->
                                     let uu____2373 =
                                       let uu____2380 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2380)  in
                                     let uu____2383 = aux formals' pats'  in
                                     uu____2373 :: uu____2383)
                             in
                          let uu___129_2398 = p1  in
                          let uu____2401 =
                            let uu____2402 =
                              let uu____2415 = aux f pats1  in
                              (fv, uu____2415)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2402  in
                          {
                            FStar_Syntax_Syntax.v = uu____2401;
                            FStar_Syntax_Syntax.p =
                              (uu___129_2398.FStar_Syntax_Syntax.p)
                          }))
            | uu____2432 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2474 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2474 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2532 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2532 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2558 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2558
                       p3.FStar_Syntax_Syntax.p
                 | uu____2581 -> (b, a, w, arg, guard, p3))
             in
          let uu____2590 = one_pat true env p  in
          match uu____2590 with
          | (b,uu____2620,uu____2621,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____2683,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2685)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2690,uu____2691) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2695 =
                    let uu____2696 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2697 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2696 uu____2697
                     in
                  failwith uu____2695)
               else ();
               (let uu____2700 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2700
                then
                  let uu____2701 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2702 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2701
                    uu____2702
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___130_2706 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___130_2706.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___130_2706.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2710 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2710
                then
                  let uu____2711 =
                    let uu____2712 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2713 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2712 uu____2713
                     in
                  failwith uu____2711
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___131_2717 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___131_2717.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___131_2717.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2719),uu____2720) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2744 =
                  let uu____2745 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2745  in
                if uu____2744
                then
                  let uu____2746 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2746
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2765;
                FStar_Syntax_Syntax.vars = uu____2766;_},args))
              ->
              ((let uu____2805 =
                  let uu____2806 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2806 Prims.op_Negation  in
                if uu____2805
                then
                  let uu____2807 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2807
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2945)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3020) ->
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
                       | ((e2,imp),uu____3057) ->
                           let pat =
                             let uu____3079 = aux argpat e2  in
                             let uu____3080 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3079, uu____3080)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3085 ->
                      let uu____3108 =
                        let uu____3109 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3110 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3109 uu____3110
                         in
                      failwith uu____3108
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3120;
                     FStar_Syntax_Syntax.vars = uu____3121;_},uu____3122);
                FStar_Syntax_Syntax.pos = uu____3123;
                FStar_Syntax_Syntax.vars = uu____3124;_},args))
              ->
              ((let uu____3167 =
                  let uu____3168 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3168 Prims.op_Negation  in
                if uu____3167
                then
                  let uu____3169 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3169
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3307)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3382) ->
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
                       | ((e2,imp),uu____3419) ->
                           let pat =
                             let uu____3441 = aux argpat e2  in
                             let uu____3442 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3441, uu____3442)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3447 ->
                      let uu____3470 =
                        let uu____3471 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3472 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3471 uu____3472
                         in
                      failwith uu____3470
                   in
                match_args [] args argpats))
          | uu____3479 ->
              let uu____3484 =
                let uu____3485 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3486 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3487 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3485 uu____3486 uu____3487
                 in
              failwith uu____3484
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
    let pat_as_arg uu____3530 =
      match uu____3530 with
      | (p,i) ->
          let uu____3547 = decorated_pattern_as_term p  in
          (match uu____3547 with
           | (vars,te) ->
               let uu____3570 =
                 let uu____3575 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3575)  in
               (vars, uu____3570))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3589 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3589)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3593 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3593)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3597 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3597)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3618 =
          let uu____3635 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3635 FStar_List.unzip  in
        (match uu____3618 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3755 =
               let uu____3756 =
                 let uu____3757 =
                   let uu____3772 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3772, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3757  in
               mk1 uu____3756  in
             (vars1, uu____3755))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3808,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3818,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3832 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3854)::[] -> wp
      | uu____3871 ->
          let uu____3880 =
            let uu____3881 =
              let uu____3882 =
                FStar_List.map
                  (fun uu____3892  ->
                     match uu____3892 with
                     | (x,uu____3898) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____3882 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3881
             in
          failwith uu____3880
       in
    let uu____3901 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____3901, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3917 = destruct_comp c  in
        match uu____3917 with
        | (u,uu____3925,wp) ->
            let uu____3927 =
              let uu____3936 =
                let uu____3943 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____3943  in
              [uu____3936]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3927;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3971 =
          let uu____3978 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____3979 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____3978 uu____3979  in
        match uu____3971 with | (m,uu____3981,uu____3982) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____3998 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____3998
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
        let uu____4041 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4041 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4078 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4078 with
             | (a,kwp) ->
                 let uu____4109 = destruct_comp m1  in
                 let uu____4116 = destruct_comp m2  in
                 ((md, a, kwp), uu____4109, uu____4116))
  
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
            let uu____4196 =
              let uu____4197 =
                let uu____4206 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4206]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4197;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4196
  
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
          let uu____4282 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4282
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
      let uu____4294 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4294
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4297  ->
           let uu____4298 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4298)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4304 =
      let uu____4305 = FStar_Syntax_Subst.compress t  in
      uu____4305.FStar_Syntax_Syntax.n  in
    match uu____4304 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4308 -> true
    | uu____4321 -> false
  
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
              let uu____4378 =
                let uu____4379 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4379  in
              if uu____4378
              then f
              else (let uu____4381 = reason1 ()  in label uu____4381 r f)
  
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
            let uu___132_4398 = g  in
            let uu____4399 =
              let uu____4400 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4400  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4399;
              FStar_TypeChecker_Env.deferred =
                (uu___132_4398.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___132_4398.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___132_4398.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4420 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4420
        then c
        else
          (let uu____4422 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4422
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4481 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4481]  in
                       let us =
                         let uu____4497 =
                           let uu____4500 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4500]  in
                         u_res :: uu____4497  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4506 =
                         let uu____4511 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4512 =
                           let uu____4513 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4520 =
                             let uu____4529 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4536 =
                               let uu____4545 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4545]  in
                             uu____4529 :: uu____4536  in
                           uu____4513 :: uu____4520  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4511 uu____4512
                          in
                       uu____4506 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4579 = destruct_comp c1  in
              match uu____4579 with
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
          (fun uu____4614  ->
             let uu____4615 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4615)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___104_4624  ->
            match uu___104_4624 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4625 -> false))
  
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
                (let uu____4647 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4647))
               &&
               (let uu____4654 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4654 with
                | (head1,uu____4668) ->
                    let uu____4685 =
                      let uu____4686 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4686.FStar_Syntax_Syntax.n  in
                    (match uu____4685 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4690 =
                           let uu____4691 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4691
                            in
                         Prims.op_Negation uu____4690
                     | uu____4692 -> true)))
              &&
              (let uu____4694 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4694)
  
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
            let uu____4728 =
              let uu____4729 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4729  in
            if uu____4728
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4731 = FStar_Syntax_Util.is_unit t  in
               if uu____4731
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
                    let uu____4737 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4737
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4739 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4739 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4749 =
                             let uu____4750 =
                               let uu____4755 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4756 =
                                 let uu____4757 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4764 =
                                   let uu____4773 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4773]  in
                                 uu____4757 :: uu____4764  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4755
                                 uu____4756
                                in
                             uu____4750 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4749)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4801 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4801
           then
             let uu____4802 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4803 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4804 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4802 uu____4803 uu____4804
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4817 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___105_4821  ->
              match uu___105_4821 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4822 -> false))
       in
    if uu____4817
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___106_4831  ->
              match uu___106_4831 with
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
        let uu____4850 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4850
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4853 = destruct_comp c1  in
           match uu____4853 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4867 =
                   let uu____4872 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4873 =
                     let uu____4874 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4881 =
                       let uu____4890 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4897 =
                         let uu____4906 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4906]  in
                       uu____4890 :: uu____4897  in
                     uu____4874 :: uu____4881  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4872 uu____4873  in
                 uu____4867 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4939 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4939)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4962 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4964 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4964
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4967 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4967 weaken
  
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
               let uu____5010 = destruct_comp c1  in
               match uu____5010 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5024 =
                       let uu____5029 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5030 =
                         let uu____5031 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5038 =
                           let uu____5047 =
                             let uu____5054 =
                               let uu____5055 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5055 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5054
                              in
                           let uu____5062 =
                             let uu____5071 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5071]  in
                           uu____5047 :: uu____5062  in
                         uu____5031 :: uu____5038  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5029 uu____5030
                        in
                     uu____5024 FStar_Pervasives_Native.None
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
            let uu____5146 =
              FStar_TypeChecker_Rel.is_trivial_guard_formula g0  in
            if uu____5146
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5155 =
                   let uu____5162 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5162
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5155 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5182 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___107_5190  ->
                               match uu___107_5190 with
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
                               | uu____5193 -> []))
                        in
                     FStar_List.append flags1 uu____5182
                  in
               let strengthen uu____5199 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5203 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5203 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5206 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5206
                          then
                            let uu____5207 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5208 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5207 uu____5208
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5210 =
                 let uu____5211 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5211
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5210,
                 (let uu___133_5213 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___133_5213.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___133_5213.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___133_5213.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___108_5220  ->
            match uu___108_5220 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5221 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5248 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5248
          then e
          else
            (let uu____5252 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5254 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5254)
                in
             if uu____5252
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
          fun uu____5304  ->
            match uu____5304 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5324 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5324 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5332 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5332
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5339 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5339
                       then
                         let uu____5342 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5342
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5346 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5346
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5351 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5351
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5355 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5355
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5364 =
                  let uu____5365 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5365
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
                       (fun uu____5379  ->
                          let uu____5380 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5381 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5383 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5380 uu____5381 uu____5383);
                     (let aux uu____5397 =
                        let uu____5398 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5398
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5419 ->
                              let uu____5420 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5420
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5439 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5439
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5510 =
                              let uu____5515 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5515, reason)  in
                            FStar_Util.Inl uu____5510
                        | uu____5522 -> aux ()  in
                      let try_simplify uu____5546 =
                        let rec maybe_close t x c =
                          let uu____5563 =
                            let uu____5564 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5564.FStar_Syntax_Syntax.n  in
                          match uu____5563 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5568) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5574 -> c  in
                        let uu____5575 =
                          let uu____5576 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5576  in
                        if uu____5575
                        then
                          let uu____5587 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____5587
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5601 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5601))
                        else
                          (let uu____5611 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5611
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5621 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5621
                              then
                                let uu____5630 =
                                  let uu____5635 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5635, "both gtot")  in
                                FStar_Util.Inl uu____5630
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5659 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5661 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____5661)
                                        in
                                     if uu____5659
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___134_5674 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___134_5674.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___134_5674.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____5675 =
                                         let uu____5680 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____5680, "c1 Tot")  in
                                       FStar_Util.Inl uu____5675
                                     else aux ()
                                 | uu____5686 -> aux ())))
                         in
                      let uu____5695 = try_simplify ()  in
                      match uu____5695 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5715  ->
                                let uu____5716 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5716);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5725  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5746 = lift_and_destruct env c11 c21
                                 in
                              match uu____5746 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5799 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5799]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5813 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5813]
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
                                    let uu____5840 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5847 =
                                      let uu____5856 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5863 =
                                        let uu____5872 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5879 =
                                          let uu____5888 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5895 =
                                            let uu____5904 =
                                              let uu____5911 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5911
                                               in
                                            [uu____5904]  in
                                          uu____5888 :: uu____5895  in
                                        uu____5872 :: uu____5879  in
                                      uu____5856 :: uu____5863  in
                                    uu____5840 :: uu____5847  in
                                  let wp =
                                    let uu____5951 =
                                      let uu____5956 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5956 wp_args
                                       in
                                    uu____5951 FStar_Pervasives_Native.None
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
                              let uu____5981 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5981 with
                              | (m,uu____5989,lift2) ->
                                  let c23 =
                                    let uu____5992 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5992
                                     in
                                  let uu____5993 = destruct_comp c12  in
                                  (match uu____5993 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6007 =
                                           let uu____6012 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6013 =
                                             let uu____6014 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6021 =
                                               let uu____6030 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6030]  in
                                             uu____6014 :: uu____6021  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6012 uu____6013
                                            in
                                         uu____6007
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
                            let uu____6061 = destruct_comp c1_typ  in
                            match uu____6061 with
                            | (u_res_t1,res_t1,uu____6070) ->
                                let uu____6071 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6071
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6074 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6074
                                   then
                                     (debug1
                                        (fun uu____6082  ->
                                           let uu____6083 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6084 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6083 uu____6084);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6089 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6091 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6091)
                                         in
                                      if uu____6089
                                      then
                                        let e1' =
                                          let uu____6111 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6111
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6120  ->
                                              let uu____6121 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6122 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6121 uu____6122);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6134  ->
                                              let uu____6135 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6136 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6135 uu____6136);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6141 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6141
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
      | uu____6157 -> g2
  
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
            (let uu____6179 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6179)
           in
        let flags1 =
          if should_return1
          then
            let uu____6185 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6185
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6197 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6201 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6201
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6205 =
              let uu____6206 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6206  in
            (if uu____6205
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___135_6211 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___135_6211.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___135_6211.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___135_6211.FStar_Syntax_Syntax.effect_args);
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
               let uu____6222 =
                 let uu____6223 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6223
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6222
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6226 =
               let uu____6227 =
                 let uu____6228 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6228
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6227  in
             FStar_Syntax_Util.comp_set_flags uu____6226 flags1)
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
            fun uu____6263  ->
              match uu____6263 with
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
                    let uu____6275 =
                      ((let uu____6278 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6278) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6275
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6292 =
        let uu____6293 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6293  in
      FStar_Syntax_Syntax.fvar uu____6292 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6359  ->
                 match uu____6359 with
                 | (uu____6372,eff_label,uu____6374,uu____6375) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6386 =
          let uu____6393 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6427  ->
                    match uu____6427 with
                    | (uu____6440,uu____6441,flags1,uu____6443) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___109_6457  ->
                                match uu___109_6457 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6458 -> false))))
             in
          if uu____6393
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6386 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6481 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6483 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6483
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6521 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6522 =
                     let uu____6527 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6528 =
                       let uu____6529 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6536 =
                         let uu____6545 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6552 =
                           let uu____6561 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6568 =
                             let uu____6577 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6577]  in
                           uu____6561 :: uu____6568  in
                         uu____6545 :: uu____6552  in
                       uu____6529 :: uu____6536  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6527 uu____6528  in
                   uu____6522 FStar_Pervasives_Native.None uu____6521  in
                 let default_case =
                   let post_k =
                     let uu____6620 =
                       let uu____6627 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6627]  in
                     let uu____6640 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6620 uu____6640  in
                   let kwp =
                     let uu____6646 =
                       let uu____6653 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6653]  in
                     let uu____6666 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6646 uu____6666  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6673 =
                       let uu____6674 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6674]  in
                     let uu____6687 =
                       let uu____6690 =
                         let uu____6697 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6697
                          in
                       let uu____6698 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6690 uu____6698  in
                     FStar_Syntax_Util.abs uu____6673 uu____6687
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
                   let uu____6720 =
                     should_not_inline_whole_match ||
                       (let uu____6722 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6722)
                      in
                   if uu____6720 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6755  ->
                        fun celse  ->
                          match uu____6755 with
                          | (g,eff_label,uu____6771,cthen) ->
                              let uu____6783 =
                                let uu____6808 =
                                  let uu____6809 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6809
                                   in
                                lift_and_destruct env uu____6808 celse  in
                              (match uu____6783 with
                               | ((md,uu____6811,uu____6812),(uu____6813,uu____6814,wp_then),
                                  (uu____6816,uu____6817,wp_else)) ->
                                   let uu____6837 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6837 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6851::[] -> comp
                 | uu____6891 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6909 = destruct_comp comp1  in
                     (match uu____6909 with
                      | (uu____6916,uu____6917,wp) ->
                          let wp1 =
                            let uu____6922 =
                              let uu____6927 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6928 =
                                let uu____6929 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6936 =
                                  let uu____6945 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6945]  in
                                uu____6929 :: uu____6936  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6927
                                uu____6928
                               in
                            uu____6922 FStar_Pervasives_Native.None
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
          let uu____7004 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7004 with
          | FStar_Pervasives_Native.None  ->
              let uu____7013 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7018 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7013 uu____7018
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
            let uu____7061 =
              let uu____7062 = FStar_Syntax_Subst.compress t2  in
              uu____7062.FStar_Syntax_Syntax.n  in
            match uu____7061 with
            | FStar_Syntax_Syntax.Tm_type uu____7065 -> true
            | uu____7066 -> false  in
          let uu____7067 =
            let uu____7068 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7068.FStar_Syntax_Syntax.n  in
          match uu____7067 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7076 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7086 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7086
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7088 =
                  let uu____7089 =
                    let uu____7090 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7090
                     in
                  (FStar_Pervasives_Native.None, uu____7089)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7088
                 in
              let e1 =
                let uu____7096 =
                  let uu____7101 =
                    let uu____7102 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7102]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7101  in
                uu____7096 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7123 -> (e, lc)
  
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
              (let uu____7160 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7160 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7183 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7205 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7205, false)
            else
              (let uu____7211 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7211, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7222) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7231 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7231 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___136_7245 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___136_7245.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___136_7245.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___136_7245.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7250 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7250 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let lc1 =
                     let uu___137_7258 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___137_7258.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___137_7258.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___137_7258.FStar_Syntax_Syntax.comp_thunk)
                     }  in
                   (e, lc1, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___138_7261 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___138_7261.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___138_7261.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___138_7261.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7267 =
                     let uu____7268 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7268
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7271 =
                          let uu____7272 = FStar_Syntax_Subst.compress f1  in
                          uu____7272.FStar_Syntax_Syntax.n  in
                        match uu____7271 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7275,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7277;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7278;_},uu____7279)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___139_7301 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___139_7301.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___139_7301.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___139_7301.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7302 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7305 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7305
                              then
                                let uu____7306 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7307 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7308 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7309 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7306 uu____7307 uu____7308 uu____7309
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
                                  let uu____7318 =
                                    let uu____7323 =
                                      let uu____7324 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7324]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7323
                                     in
                                  uu____7318 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7346 =
                                let uu____7351 =
                                  FStar_All.pipe_left
                                    (fun _0_17  ->
                                       FStar_Pervasives_Native.Some _0_17)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7368 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7369 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7370 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7351 uu____7368
                                  e uu____7369 uu____7370
                                 in
                              match uu____7346 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___140_7374 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___140_7374.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___140_7374.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7376 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7376
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7381 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7381
                                    then
                                      let uu____7382 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7382
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___110_7392  ->
                             match uu___110_7392 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7395 -> []))
                      in
                   let lc1 =
                     let uu____7397 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7397 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___141_7399 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___141_7399.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___141_7399.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___141_7399.FStar_TypeChecker_Env.implicits)
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
        let uu____7434 =
          let uu____7437 =
            let uu____7442 =
              let uu____7443 =
                let uu____7450 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7450  in
              [uu____7443]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7442  in
          uu____7437 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7434  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7471 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7471
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7487 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7502 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7518 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7518
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7532)::(ens,uu____7534)::uu____7535 ->
                    let uu____7564 =
                      let uu____7567 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7567  in
                    let uu____7568 =
                      let uu____7569 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7569  in
                    (uu____7564, uu____7568)
                | uu____7572 ->
                    let uu____7581 =
                      let uu____7586 =
                        let uu____7587 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7587
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7586)
                       in
                    FStar_Errors.raise_error uu____7581
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7603)::uu____7604 ->
                    let uu____7623 =
                      let uu____7628 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7628
                       in
                    (match uu____7623 with
                     | (us_r,uu____7660) ->
                         let uu____7661 =
                           let uu____7666 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7666
                            in
                         (match uu____7661 with
                          | (us_e,uu____7698) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____7701 =
                                  let uu____7702 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7702
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7701
                                  us_r
                                 in
                              let as_ens =
                                let uu____7704 =
                                  let uu____7705 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7705
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7704
                                  us_e
                                 in
                              let req =
                                let uu____7709 =
                                  let uu____7714 =
                                    let uu____7715 =
                                      let uu____7724 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7724]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7715
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7714
                                   in
                                uu____7709 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____7756 =
                                  let uu____7761 =
                                    let uu____7762 =
                                      let uu____7771 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7771]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7762
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7761
                                   in
                                uu____7756 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____7800 =
                                let uu____7803 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____7803  in
                              let uu____7804 =
                                let uu____7805 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____7805  in
                              (uu____7800, uu____7804)))
                | uu____7808 -> failwith "Impossible"))
  
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
      (let uu____7838 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____7838
       then
         let uu____7839 = FStar_Syntax_Print.term_to_string tm  in
         let uu____7840 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7839 uu____7840
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
        (let uu____7884 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____7884
         then
           let uu____7885 = FStar_Syntax_Print.term_to_string tm  in
           let uu____7886 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7885
             uu____7886
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____7893 =
      let uu____7894 =
        let uu____7895 = FStar_Syntax_Subst.compress t  in
        uu____7895.FStar_Syntax_Syntax.n  in
      match uu____7894 with
      | FStar_Syntax_Syntax.Tm_app uu____7898 -> false
      | uu____7913 -> true  in
    if uu____7893
    then t
    else
      (let uu____7915 = FStar_Syntax_Util.head_and_args t  in
       match uu____7915 with
       | (head1,args) ->
           let uu____7952 =
             let uu____7953 =
               let uu____7954 = FStar_Syntax_Subst.compress head1  in
               uu____7954.FStar_Syntax_Syntax.n  in
             match uu____7953 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7957 -> false  in
           if uu____7952
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7979 ->
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
             let uu____8024 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8024 with
             | (formals,uu____8038) ->
                 let n_implicits =
                   let uu____8056 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8134  ->
                             match uu____8134 with
                             | (uu____8141,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8056 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8274 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8274 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8298 =
                     let uu____8303 =
                       let uu____8304 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8311 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8312 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8304 uu____8311 uu____8312
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8303)
                      in
                   let uu____8319 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8298 uu____8319
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___111_8342 =
             match uu___111_8342 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8372 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8372 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_18,uu____8487) when
                          _0_18 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8530,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8563 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8563 with
                           | (v1,uu____8603,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____8622 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____8622 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8715 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8715)))
                      | (uu____8742,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____8788 =
                      let uu____8815 = inst_n_binders t  in
                      aux [] uu____8815 bs1  in
                    (match uu____8788 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8886) -> (e, torig, guard)
                          | (uu____8917,[]) when
                              let uu____8948 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8948 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8949 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8977 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8990 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9000 =
      let uu____9003 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9003
        (FStar_List.map
           (fun u  ->
              let uu____9013 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9013 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9000 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9034 = FStar_Util.set_is_empty x  in
      if uu____9034
      then []
      else
        (let s =
           let uu____9049 =
             let uu____9052 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9052  in
           FStar_All.pipe_right uu____9049 FStar_Util.set_elements  in
         (let uu____9068 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9068
          then
            let uu____9069 =
              let uu____9070 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9070  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9069
          else ());
         (let r =
            let uu____9077 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9077  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9116 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9116
                     then
                       let uu____9117 =
                         let uu____9118 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9118
                          in
                       let uu____9119 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9120 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9117 uu____9119 uu____9120
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
        let uu____9146 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9146 FStar_Util.set_elements  in
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
        | ([],uu____9184) -> generalized_univ_names
        | (uu____9191,[]) -> explicit_univ_names
        | uu____9198 ->
            let uu____9207 =
              let uu____9212 =
                let uu____9213 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9213
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9212)
               in
            FStar_Errors.raise_error uu____9207 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9231 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9231
       then
         let uu____9232 = FStar_Syntax_Print.term_to_string t  in
         let uu____9233 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9232 uu____9233
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9239 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9239
        then
          let uu____9240 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9240
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9246 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9246
         then
           let uu____9247 = FStar_Syntax_Print.term_to_string t  in
           let uu____9248 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9247 uu____9248
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
        let uu____9326 =
          let uu____9327 =
            FStar_Util.for_all
              (fun uu____9340  ->
                 match uu____9340 with
                 | (uu____9349,uu____9350,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9327  in
        if uu____9326
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9398 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9398
              then
                let uu____9399 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9399
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9403 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9403
               then
                 let uu____9404 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9404
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9419 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9419 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9455 =
             match uu____9455 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9499 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9499
                   then
                     let uu____9500 =
                       let uu____9501 =
                         let uu____9504 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9504
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9501
                         (FStar_String.concat ", ")
                        in
                     let uu____9547 =
                       let uu____9548 =
                         let uu____9551 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9551
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9562 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9563 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9562
                                   uu____9563))
                          in
                       FStar_All.pipe_right uu____9548
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9500
                       uu____9547
                   else ());
                  (let univs2 =
                     let uu____9570 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____9582 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____9582) univs1
                       uu____9570
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____9589 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____9589
                    then
                      let uu____9590 =
                        let uu____9591 =
                          let uu____9594 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____9594
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____9591
                          (FStar_String.concat ", ")
                         in
                      let uu____9637 =
                        let uu____9638 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____9649 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____9650 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____9649
                                    uu____9650))
                           in
                        FStar_All.pipe_right uu____9638
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9590
                        uu____9637
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____9664 =
             let uu____9681 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____9681  in
           match uu____9664 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9773 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9773
                 then ()
                 else
                   (let uu____9775 = lec_hd  in
                    match uu____9775 with
                    | (lb1,uu____9783,uu____9784) ->
                        let uu____9785 = lec2  in
                        (match uu____9785 with
                         | (lb2,uu____9793,uu____9794) ->
                             let msg =
                               let uu____9796 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9797 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9796 uu____9797
                                in
                             let uu____9798 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9798))
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
                 let uu____9862 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9862
                 then ()
                 else
                   (let uu____9864 = lec_hd  in
                    match uu____9864 with
                    | (lb1,uu____9872,uu____9873) ->
                        let uu____9874 = lec2  in
                        (match uu____9874 with
                         | (lb2,uu____9882,uu____9883) ->
                             let msg =
                               let uu____9885 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9886 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9885 uu____9886
                                in
                             let uu____9887 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9887))
                  in
               let lecs1 =
                 let uu____9897 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9956 = univs_and_uvars_of_lec this_lec  in
                        match uu____9956 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9897 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10057 = lec_hd  in
                   match uu____10057 with
                   | (lbname,e,c) ->
                       let uu____10067 =
                         let uu____10072 =
                           let uu____10073 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10074 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10075 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10073 uu____10074 uu____10075
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10072)
                          in
                       let uu____10076 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10067 uu____10076
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10097 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10097 with
                         | FStar_Pervasives_Native.Some uu____10106 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10113 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10117 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10117 with
                              | (bs,kres) ->
                                  ((let uu____10155 =
                                      let uu____10156 =
                                        let uu____10159 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10159
                                         in
                                      uu____10156.FStar_Syntax_Syntax.n  in
                                    match uu____10155 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10160
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10164 =
                                          let uu____10165 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10165  in
                                        if uu____10164
                                        then fail1 kres
                                        else ()
                                    | uu____10167 -> fail1 kres);
                                   (let a =
                                      let uu____10169 =
                                        let uu____10172 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_19  ->
                                             FStar_Pervasives_Native.Some
                                               _0_19) uu____10172
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10169
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10180 ->
                                          let uu____10187 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10187
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
                      (fun uu____10298  ->
                         match uu____10298 with
                         | (lbname,e,c) ->
                             let uu____10352 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10427 ->
                                   let uu____10442 = (e, c)  in
                                   (match uu____10442 with
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
                                                (fun uu____10493  ->
                                                   match uu____10493 with
                                                   | (x,uu____10501) ->
                                                       let uu____10506 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10506)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10524 =
                                                let uu____10525 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10525
                                                 in
                                              if uu____10524
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
                                          let uu____10531 =
                                            let uu____10532 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10532.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10531 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10553 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10553 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10566 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10570 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10570, gen_tvars))
                                in
                             (match uu____10352 with
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
        (let uu____10724 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10724
         then
           let uu____10725 =
             let uu____10726 =
               FStar_List.map
                 (fun uu____10739  ->
                    match uu____10739 with
                    | (lb,uu____10747,uu____10748) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10726 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10725
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10769  ->
                match uu____10769 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10798 = gen env is_rec lecs  in
           match uu____10798 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10897  ->
                       match uu____10897 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10959 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10959
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11005  ->
                           match uu____11005 with
                           | (l,us,e,c,gvs) ->
                               let uu____11039 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11040 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11041 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11042 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11043 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11039 uu____11040 uu____11041
                                 uu____11042 uu____11043))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11084  ->
                match uu____11084 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11128 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11128, t, c, gvs)) univnames_lecs
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
              (let uu____11185 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11185 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11191 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_20  -> FStar_Pervasives_Native.Some _0_20)
                     uu____11191)
             in
          let is_var e1 =
            let uu____11200 =
              let uu____11201 = FStar_Syntax_Subst.compress e1  in
              uu____11201.FStar_Syntax_Syntax.n  in
            match uu____11200 with
            | FStar_Syntax_Syntax.Tm_name uu____11204 -> true
            | uu____11205 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___142_11225 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___142_11225.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___142_11225.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11226 -> e2  in
          let env2 =
            let uu___143_11228 = env1  in
            let uu____11229 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___143_11228.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___143_11228.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___143_11228.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___143_11228.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___143_11228.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___143_11228.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___143_11228.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___143_11228.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___143_11228.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___143_11228.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___143_11228.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___143_11228.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___143_11228.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___143_11228.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___143_11228.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___143_11228.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11229;
              FStar_TypeChecker_Env.is_iface =
                (uu___143_11228.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___143_11228.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___143_11228.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___143_11228.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___143_11228.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___143_11228.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.tc_term =
                (uu___143_11228.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___143_11228.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___143_11228.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___143_11228.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___143_11228.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___143_11228.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___143_11228.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___143_11228.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___143_11228.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___143_11228.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___143_11228.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___143_11228.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___143_11228.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___143_11228.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___143_11228.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11230 = check1 env2 t1 t2  in
          match uu____11230 with
          | FStar_Pervasives_Native.None  ->
              let uu____11237 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11242 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11237 uu____11242
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11249 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11249
                then
                  let uu____11250 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11250
                else ());
               (let uu____11252 = decorate e t2  in (uu____11252, g)))
  
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
        let uu____11284 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11284
        then
          let uu____11289 = discharge g1  in
          let uu____11290 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11289, uu____11290)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11297 =
               let uu____11298 =
                 let uu____11299 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11299 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11298
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11297
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11301 = destruct_comp c1  in
           match uu____11301 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11318 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11319 =
                   let uu____11324 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11325 =
                     let uu____11326 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11333 =
                       let uu____11342 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11342]  in
                     uu____11326 :: uu____11333  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11324 uu____11325  in
                 uu____11319 FStar_Pervasives_Native.None uu____11318  in
               ((let uu____11370 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11370
                 then
                   let uu____11371 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11371
                 else ());
                (let g2 =
                   let uu____11374 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11374  in
                 let uu____11375 = discharge g2  in
                 let uu____11376 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11375, uu____11376))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___112_11408 =
        match uu___112_11408 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11416)::[] -> f fst1
        | uu____11433 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11444 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11444
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_or_e e =
        let uu____11455 =
          let uu____11456 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11456  in
        FStar_All.pipe_right uu____11455
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_or_t t =
        let uu____11475 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11475
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
         in
      let short_op_ite uu___113_11489 =
        match uu___113_11489 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11497)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11516)::[] ->
            let uu____11545 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11545
              (fun _0_26  -> FStar_TypeChecker_Common.NonTrivial _0_26)
        | uu____11546 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11557 =
          let uu____11565 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11565)  in
        let uu____11573 =
          let uu____11583 =
            let uu____11591 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____11591)  in
          let uu____11599 =
            let uu____11609 =
              let uu____11617 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____11617)  in
            let uu____11625 =
              let uu____11635 =
                let uu____11643 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____11643)  in
              let uu____11651 =
                let uu____11661 =
                  let uu____11669 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____11669)  in
                [uu____11661; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____11635 :: uu____11651  in
            uu____11609 :: uu____11625  in
          uu____11583 :: uu____11599  in
        uu____11557 :: uu____11573  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11731 =
            FStar_Util.find_map table
              (fun uu____11746  ->
                 match uu____11746 with
                 | (x,mk1) ->
                     let uu____11763 = FStar_Ident.lid_equals x lid  in
                     if uu____11763
                     then
                       let uu____11766 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11766
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11731 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11769 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11775 =
      let uu____11776 = FStar_Syntax_Util.un_uinst l  in
      uu____11776.FStar_Syntax_Syntax.n  in
    match uu____11775 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11780 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11810)::uu____11811 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11822 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11829,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11830))::uu____11831 -> bs
      | uu____11842 ->
          let uu____11843 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11843 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11847 =
                 let uu____11848 = FStar_Syntax_Subst.compress t  in
                 uu____11848.FStar_Syntax_Syntax.n  in
               (match uu____11847 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11852) ->
                    let uu____11869 =
                      FStar_Util.prefix_until
                        (fun uu___114_11909  ->
                           match uu___114_11909 with
                           | (uu____11916,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11917)) ->
                               false
                           | uu____11920 -> true) bs'
                       in
                    (match uu____11869 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11955,uu____11956) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12028,uu____12029) ->
                         let uu____12102 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12120  ->
                                   match uu____12120 with
                                   | (x,uu____12128) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12102
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12171  ->
                                     match uu____12171 with
                                     | (x,i) ->
                                         let uu____12190 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12190, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12198 -> bs))
  
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
            let uu____12226 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12226
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
          let uu____12253 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12253
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
        (let uu____12288 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12288
         then
           ((let uu____12290 = FStar_Ident.text_of_lid lident  in
             d uu____12290);
            (let uu____12291 = FStar_Ident.text_of_lid lident  in
             let uu____12292 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12291 uu____12292))
         else ());
        (let fv =
           let uu____12295 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12295
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
         let uu____12305 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___144_12307 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___144_12307.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___144_12307.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___144_12307.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___144_12307.FStar_Syntax_Syntax.sigattrs)
           }), uu____12305))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___115_12323 =
        match uu___115_12323 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12324 -> false  in
      let reducibility uu___116_12330 =
        match uu___116_12330 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12331 -> false  in
      let assumption uu___117_12337 =
        match uu___117_12337 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12338 -> false  in
      let reification uu___118_12344 =
        match uu___118_12344 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12345 -> true
        | uu____12346 -> false  in
      let inferred uu___119_12352 =
        match uu___119_12352 with
        | FStar_Syntax_Syntax.Discriminator uu____12353 -> true
        | FStar_Syntax_Syntax.Projector uu____12354 -> true
        | FStar_Syntax_Syntax.RecordType uu____12359 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12368 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12377 -> false  in
      let has_eq uu___120_12383 =
        match uu___120_12383 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12384 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12448 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12453 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12457 =
        let uu____12458 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___121_12462  ->
                  match uu___121_12462 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12463 -> false))
           in
        FStar_All.pipe_right uu____12458 Prims.op_Negation  in
      if uu____12457
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12478 =
            let uu____12483 =
              let uu____12484 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12484 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12483)  in
          FStar_Errors.raise_error uu____12478 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12496 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12500 =
            let uu____12501 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12501  in
          if uu____12500 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12506),uu____12507) ->
              ((let uu____12517 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12517
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12521 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12521
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12527 ->
              let uu____12536 =
                let uu____12537 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12537  in
              if uu____12536 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12543 ->
              let uu____12550 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12550 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12554 ->
              let uu____12561 =
                let uu____12562 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12562  in
              if uu____12561 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12568 ->
              let uu____12569 =
                let uu____12570 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12570  in
              if uu____12569 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12576 ->
              let uu____12577 =
                let uu____12578 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12578  in
              if uu____12577 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12584 ->
              let uu____12597 =
                let uu____12598 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____12598  in
              if uu____12597 then err'1 () else ()
          | uu____12604 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____12638 =
          let uu____12639 = FStar_Syntax_Subst.compress t1  in
          uu____12639.FStar_Syntax_Syntax.n  in
        match uu____12638 with
        | FStar_Syntax_Syntax.Tm_type uu____12642 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____12645 =
                 let uu____12650 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____12650
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____12645
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____12668 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____12668
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____12685 =
                                 let uu____12686 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____12686.FStar_Syntax_Syntax.n  in
                               match uu____12685 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____12690 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____12691 ->
            let uu____12704 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____12704 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____12730 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____12730
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____12732;
               FStar_Syntax_Syntax.index = uu____12733;
               FStar_Syntax_Syntax.sort = t2;_},uu____12735)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12743,uu____12744) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____12786::[]) ->
            let uu____12817 =
              let uu____12818 = FStar_Syntax_Util.un_uinst head1  in
              uu____12818.FStar_Syntax_Syntax.n  in
            (match uu____12817 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____12822 -> false)
        | uu____12823 -> false
      
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
        (let uu____12831 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____12831
         then
           let uu____12832 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____12832
         else ());
        res
       in aux g t
  