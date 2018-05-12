open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
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
                    let uu___118_199 = FStar_TypeChecker_Rel.trivial_guard
                       in
                    {
                      FStar_TypeChecker_Env.guard_f =
                        (uu___118_199.FStar_TypeChecker_Env.guard_f);
                      FStar_TypeChecker_Env.deferred =
                        (uu___118_199.FStar_TypeChecker_Env.deferred);
                      FStar_TypeChecker_Env.univ_ineqs =
                        (uu___118_199.FStar_TypeChecker_Env.univ_ineqs);
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
          let uu____280 = FStar_Options.eager_subtyping ()  in
          FStar_All.pipe_left Prims.op_Negation uu____280  in
        if uu____279
        then g
        else
          (let uu____282 =
             FStar_All.pipe_right g.FStar_TypeChecker_Env.deferred
               (FStar_List.partition
                  (fun uu____328  ->
                     match uu____328 with
                     | (uu____333,p) ->
                         FStar_TypeChecker_Rel.flex_prob_closing env xs p))
              in
           match uu____282 with
           | (solve_now,defer) ->
               ((let uu____362 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____362
                 then
                   (FStar_Util.print_string "SOLVE BEFORE CLOSING:\n";
                    FStar_List.iter
                      (fun uu____373  ->
                         match uu____373 with
                         | (s,p) ->
                             let uu____380 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____380)
                      solve_now;
                    FStar_Util.print_string " ...DEFERRED THE REST:\n";
                    FStar_List.iter
                      (fun uu____391  ->
                         match uu____391 with
                         | (s,p) ->
                             let uu____398 =
                               FStar_TypeChecker_Rel.prob_to_string env p  in
                             FStar_Util.print2 "%s: %s\n" s uu____398) defer;
                    FStar_Util.print_string "END\n")
                 else ());
                (let g1 =
                   FStar_TypeChecker_Rel.solve_deferred_constraints env
                     (let uu___119_402 = g  in
                      {
                        FStar_TypeChecker_Env.guard_f =
                          (uu___119_402.FStar_TypeChecker_Env.guard_f);
                        FStar_TypeChecker_Env.deferred = solve_now;
                        FStar_TypeChecker_Env.univ_ineqs =
                          (uu___119_402.FStar_TypeChecker_Env.univ_ineqs);
                        FStar_TypeChecker_Env.implicits =
                          (uu___119_402.FStar_TypeChecker_Env.implicits)
                      })
                    in
                 let g2 =
                   let uu___120_404 = g1  in
                   {
                     FStar_TypeChecker_Env.guard_f =
                       (uu___120_404.FStar_TypeChecker_Env.guard_f);
                     FStar_TypeChecker_Env.deferred = defer;
                     FStar_TypeChecker_Env.univ_ineqs =
                       (uu___120_404.FStar_TypeChecker_Env.univ_ineqs);
                     FStar_TypeChecker_Env.implicits =
                       (uu___120_404.FStar_TypeChecker_Env.implicits)
                   }  in
                 g2)))
  
let (check_uvars : FStar_Range.range -> FStar_Syntax_Syntax.typ -> unit) =
  fun r  ->
    fun t  ->
      let uvs = FStar_Syntax_Free.uvars t  in
      let uu____418 =
        let uu____419 = FStar_Util.set_is_empty uvs  in
        Prims.op_Negation uu____419  in
      if uu____418
      then
        let us =
          let uu____421 =
            let uu____424 = FStar_Util.set_elements uvs  in
            FStar_List.map
              (fun u  ->
                 FStar_Syntax_Print.uvar_to_string
                   u.FStar_Syntax_Syntax.ctx_uvar_head) uu____424
             in
          FStar_All.pipe_right uu____421 (FStar_String.concat ", ")  in
        (FStar_Options.push ();
         FStar_Options.set_option "hide_uvar_nums" (FStar_Options.Bool false);
         FStar_Options.set_option "print_implicits" (FStar_Options.Bool true);
         (let uu____435 =
            let uu____440 =
              let uu____441 = FStar_Syntax_Print.term_to_string t  in
              FStar_Util.format2
                "Unconstrained unification variables %s in type signature %s; please add an annotation"
                us uu____441
               in
            (FStar_Errors.Error_UncontrainedUnificationVar, uu____440)  in
          FStar_Errors.log_issue r uu____435);
         FStar_Options.pop ())
      else ()
  
let (extract_let_rec_annotation :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.letbinding ->
      (FStar_Syntax_Syntax.univ_names,FStar_Syntax_Syntax.typ,Prims.bool)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun uu____458  ->
      match uu____458 with
      | { FStar_Syntax_Syntax.lbname = lbname;
          FStar_Syntax_Syntax.lbunivs = univ_vars1;
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = uu____468;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = uu____470;
          FStar_Syntax_Syntax.lbpos = uu____471;_} ->
          let rng = FStar_Syntax_Syntax.range_of_lbname lbname  in
          let t1 = FStar_Syntax_Subst.compress t  in
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               let uu____504 = FStar_Syntax_Subst.open_univ_vars univ_vars1 e
                  in
               (match uu____504 with
                | (univ_vars2,e1) ->
                    let env1 =
                      FStar_TypeChecker_Env.push_univ_vars env univ_vars2  in
                    let r = FStar_TypeChecker_Env.get_range env1  in
                    let rec aux e2 =
                      let e3 = FStar_Syntax_Subst.compress e2  in
                      match e3.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_meta (e4,uu____541) -> aux e4
                      | FStar_Syntax_Syntax.Tm_ascribed (e4,t2,uu____548) ->
                          FStar_Pervasives_Native.fst t2
                      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____603) ->
                          let res = aux body  in
                          let c =
                            match res with
                            | FStar_Util.Inl t2 ->
                                let uu____635 = FStar_Options.ml_ish ()  in
                                if uu____635
                                then FStar_Syntax_Util.ml_comp t2 r
                                else FStar_Syntax_Syntax.mk_Total t2
                            | FStar_Util.Inr c -> c  in
                          let t2 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                              FStar_Pervasives_Native.None
                              c.FStar_Syntax_Syntax.pos
                             in
                          ((let uu____652 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.High
                               in
                            if uu____652
                            then
                              let uu____653 = FStar_Range.string_of_range r
                                 in
                              let uu____654 =
                                FStar_Syntax_Print.term_to_string t2  in
                              FStar_Util.print2 "(%s) Using type %s\n"
                                uu____653 uu____654
                            else ());
                           FStar_Util.Inl t2)
                      | uu____656 -> FStar_Util.Inl FStar_Syntax_Syntax.tun
                       in
                    let t2 =
                      let uu____658 = aux e1  in
                      match uu____658 with
                      | FStar_Util.Inr c ->
                          let uu____664 =
                            FStar_Syntax_Util.is_tot_or_gtot_comp c  in
                          if uu____664
                          then FStar_Syntax_Util.comp_result c
                          else
                            (let uu____666 =
                               let uu____671 =
                                 let uu____672 =
                                   FStar_Syntax_Print.comp_to_string c  in
                                 FStar_Util.format1
                                   "Expected a 'let rec' to be annotated with a value type; got a computation type %s"
                                   uu____672
                                  in
                               (FStar_Errors.Fatal_UnexpectedComputationTypeForLetRec,
                                 uu____671)
                                in
                             FStar_Errors.raise_error uu____666 rng)
                      | FStar_Util.Inl t2 -> t2  in
                    (univ_vars2, t2, true))
           | uu____676 ->
               let uu____677 =
                 FStar_Syntax_Subst.open_univ_vars univ_vars1 t1  in
               (match uu____677 with
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
            let uu____771 =
              let uu____778 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____778 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____785;
                  FStar_Syntax_Syntax.vars = uu____786;_} ->
                  let uu____789 = FStar_Syntax_Util.type_u ()  in
                  (match uu____789 with
                   | (t,uu____801) ->
                       let uu____802 =
                         let uu____817 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         new_implicit_var_aux "pattern bv type" uu____817
                           env1 t FStar_Syntax_Syntax.Allow_untyped
                          in
                       (match uu____802 with | (t1,uu____825,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____771 with
            | (t_x,guard) ->
                ((let uu___121_857 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___121_857.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___121_857.FStar_Syntax_Syntax.index);
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
                       let uu____987 = FStar_Syntax_Syntax.range_of_bv x  in
                       new_implicit_var_aux "pat_dot_term type" uu____987
                         env1 k FStar_Syntax_Syntax.Allow_untyped
                        in
                     (match uu____972 with
                      | (t,uu____1009,g) ->
                          let x1 =
                            let uu___122_1028 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___122_1028.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___122_1028.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____1029 =
                            let uu____1044 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            new_implicit_var_aux "pat_dot_term" uu____1044
                              env1 t FStar_Syntax_Syntax.Allow_untyped
                             in
                          (match uu____1029 with
                           | (e,uu____1066,g') ->
                               let p2 =
                                 let uu___123_1087 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___123_1087.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____1090 =
                                 FStar_TypeChecker_Rel.conj_guard g g'  in
                               ([], [], [], env1, e, uu____1090, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____1098 = check_bv env1 x  in
                (match uu____1098 with
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
                let uu____1137 = check_bv env1 x  in
                (match uu____1137 with
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
                let uu____1192 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____1326  ->
                          fun uu____1327  ->
                            match (uu____1326, uu____1327) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____1525 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____1525 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____1601 =
                                       FStar_TypeChecker_Rel.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____1601, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Rel.trivial_guard, []))
                   in
                (match uu____1192 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1732 =
                         let uu____1737 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1738 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1737 uu____1738
                          in
                       uu____1732 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1755 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1766 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1777 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1755, uu____1766, uu____1777, env2, e, guard,
                       (let uu___124_1795 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___124_1795.FStar_Syntax_Syntax.p)
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
                    (fun uu____1895  ->
                       match uu____1895 with
                       | (p2,imp) ->
                           let uu____1914 = elaborate_pat env1 p2  in
                           (uu____1914, imp)) pats
                   in
                let uu____1919 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____1919 with
                 | (uu____1926,t) ->
                     let uu____1928 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____1928 with
                      | (f,uu____1944) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____2070::uu____2071) ->
                                let uu____2114 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____2114
                            | (uu____2123::uu____2124,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____2202  ->
                                        match uu____2202 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____2229 =
                                                     let uu____2232 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____2232
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____2229
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____2234 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____2234, true)
                                             | uu____2239 ->
                                                 let uu____2242 =
                                                   let uu____2247 =
                                                     let uu____2248 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____2248
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____2247)
                                                    in
                                                 let uu____2249 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____2242 uu____2249)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____2323,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____2324)) when p_imp ->
                                     let uu____2327 = aux formals' pats'  in
                                     (p2, true) :: uu____2327
                                 | (uu____2344,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____2352 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____2352
                                        in
                                     let uu____2353 = aux formals' pats2  in
                                     (p3, true) :: uu____2353
                                 | (uu____2370,imp) ->
                                     let uu____2376 =
                                       let uu____2383 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____2383)  in
                                     let uu____2386 = aux formals' pats'  in
                                     uu____2376 :: uu____2386)
                             in
                          let uu___125_2401 = p1  in
                          let uu____2404 =
                            let uu____2405 =
                              let uu____2418 = aux f pats1  in
                              (fv, uu____2418)  in
                            FStar_Syntax_Syntax.Pat_cons uu____2405  in
                          {
                            FStar_Syntax_Syntax.v = uu____2404;
                            FStar_Syntax_Syntax.p =
                              (uu___125_2401.FStar_Syntax_Syntax.p)
                          }))
            | uu____2435 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____2477 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____2477 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____2535 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____2535 with
                 | FStar_Pervasives_Native.Some x ->
                     let uu____2561 =
                       FStar_TypeChecker_Err.nonlinear_pattern_variable x  in
                     FStar_Errors.raise_error uu____2561
                       p3.FStar_Syntax_Syntax.p
                 | uu____2584 -> (b, a, w, arg, guard, p3))
             in
          let uu____2593 = one_pat true env p  in
          match uu____2593 with
          | (b,uu____2623,uu____2624,tm,guard,p1) -> (b, tm, guard, p1)
  
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
          | (uu____2686,FStar_Syntax_Syntax.Tm_uinst (e2,uu____2688)) ->
              aux p1 e2
          | (FStar_Syntax_Syntax.Pat_constant uu____2693,uu____2694) ->
              pkg p1.FStar_Syntax_Syntax.v
          | (FStar_Syntax_Syntax.Pat_var x,FStar_Syntax_Syntax.Tm_name y) ->
              (if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x y)
               then
                 (let uu____2698 =
                    let uu____2699 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2700 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2699 uu____2700
                     in
                  failwith uu____2698)
               else ();
               (let uu____2703 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Pat")
                   in
                if uu____2703
                then
                  let uu____2704 = FStar_Syntax_Print.bv_to_string x  in
                  let uu____2705 =
                    FStar_TypeChecker_Normalize.term_to_string env
                      y.FStar_Syntax_Syntax.sort
                     in
                  FStar_Util.print2
                    "Pattern variable %s introduced at type %s\n" uu____2704
                    uu____2705
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___126_2709 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___126_2709.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___126_2709.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_var x1)))
          | (FStar_Syntax_Syntax.Pat_wild x,FStar_Syntax_Syntax.Tm_name y) ->
              ((let uu____2713 =
                  FStar_All.pipe_right (FStar_Syntax_Syntax.bv_eq x y)
                    Prims.op_Negation
                   in
                if uu____2713
                then
                  let uu____2714 =
                    let uu____2715 = FStar_Syntax_Print.bv_to_string x  in
                    let uu____2716 = FStar_Syntax_Print.bv_to_string y  in
                    FStar_Util.format2 "Expected pattern variable %s; got %s"
                      uu____2715 uu____2716
                     in
                  failwith uu____2714
                else ());
               (let s =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta] env
                    y.FStar_Syntax_Syntax.sort
                   in
                let x1 =
                  let uu___127_2720 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___127_2720.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___127_2720.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = s
                  }  in
                pkg (FStar_Syntax_Syntax.Pat_wild x1)))
          | (FStar_Syntax_Syntax.Pat_dot_term (x,uu____2722),uu____2723) ->
              pkg (FStar_Syntax_Syntax.Pat_dot_term (x, e1))
          | (FStar_Syntax_Syntax.Pat_cons (fv,[]),FStar_Syntax_Syntax.Tm_fvar
             fv') ->
              ((let uu____2747 =
                  let uu____2748 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  Prims.op_Negation uu____2748  in
                if uu____2747
                then
                  let uu____2749 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2749
                else ());
               pkg (FStar_Syntax_Syntax.Pat_cons (fv', [])))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                FStar_Syntax_Syntax.pos = uu____2768;
                FStar_Syntax_Syntax.vars = uu____2769;_},args))
              ->
              ((let uu____2808 =
                  let uu____2809 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____2809 Prims.op_Negation  in
                if uu____2808
                then
                  let uu____2810 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____2810
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____2948)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3023) ->
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
                       | ((e2,imp),uu____3060) ->
                           let pat =
                             let uu____3082 = aux argpat e2  in
                             let uu____3083 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3082, uu____3083)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3088 ->
                      let uu____3111 =
                        let uu____3112 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3113 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3112 uu____3113
                         in
                      failwith uu____3111
                   in
                match_args [] args argpats))
          | (FStar_Syntax_Syntax.Pat_cons
             (fv,argpats),FStar_Syntax_Syntax.Tm_app
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                  ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv';
                     FStar_Syntax_Syntax.pos = uu____3123;
                     FStar_Syntax_Syntax.vars = uu____3124;_},uu____3125);
                FStar_Syntax_Syntax.pos = uu____3126;
                FStar_Syntax_Syntax.vars = uu____3127;_},args))
              ->
              ((let uu____3170 =
                  let uu____3171 = FStar_Syntax_Syntax.fv_eq fv fv'  in
                  FStar_All.pipe_right uu____3171 Prims.op_Negation  in
                if uu____3170
                then
                  let uu____3172 =
                    FStar_Util.format2
                      "Expected pattern constructor %s; got %s"
                      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                      ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                     in
                  failwith uu____3172
                else ());
               (let fv1 = fv'  in
                let rec match_args matched_pats args1 argpats1 =
                  match (args1, argpats1) with
                  | ([],[]) ->
                      pkg
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv1, (FStar_List.rev matched_pats)))
                  | (arg::args2,(argpat,uu____3310)::argpats2) ->
                      (match (arg, (argpat.FStar_Syntax_Syntax.v)) with
                       | ((e2,FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Implicit (true ))),FStar_Syntax_Syntax.Pat_dot_term
                          uu____3385) ->
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
                       | ((e2,imp),uu____3422) ->
                           let pat =
                             let uu____3444 = aux argpat e2  in
                             let uu____3445 =
                               FStar_Syntax_Syntax.is_implicit imp  in
                             (uu____3444, uu____3445)  in
                           match_args (pat :: matched_pats) args2 argpats2)
                  | uu____3450 ->
                      let uu____3473 =
                        let uu____3474 = FStar_Syntax_Print.pat_to_string p1
                           in
                        let uu____3475 = FStar_Syntax_Print.term_to_string e1
                           in
                        FStar_Util.format2
                          "Unexpected number of pattern arguments: \n\t%s\n\t%s\n"
                          uu____3474 uu____3475
                         in
                      failwith uu____3473
                   in
                match_args [] args argpats))
          | uu____3482 ->
              let uu____3487 =
                let uu____3488 =
                  FStar_Range.string_of_range qq.FStar_Syntax_Syntax.p  in
                let uu____3489 = FStar_Syntax_Print.pat_to_string qq  in
                let uu____3490 = FStar_Syntax_Print.term_to_string exp  in
                FStar_Util.format3
                  "(%s) Impossible: pattern to decorate is %s; expression is %s\n"
                  uu____3488 uu____3489 uu____3490
                 in
              failwith uu____3487
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
    let pat_as_arg uu____3533 =
      match uu____3533 with
      | (p,i) ->
          let uu____3550 = decorated_pattern_as_term p  in
          (match uu____3550 with
           | (vars,te) ->
               let uu____3573 =
                 let uu____3578 = FStar_Syntax_Syntax.as_implicit i  in
                 (te, uu____3578)  in
               (vars, uu____3573))
       in
    match pat.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu____3592 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
        ([], uu____3592)
    | FStar_Syntax_Syntax.Pat_wild x ->
        let uu____3596 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3596)
    | FStar_Syntax_Syntax.Pat_var x ->
        let uu____3600 = mk1 (FStar_Syntax_Syntax.Tm_name x)  in
        ([x], uu____3600)
    | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
        let uu____3621 =
          let uu____3638 =
            FStar_All.pipe_right pats (FStar_List.map pat_as_arg)  in
          FStar_All.pipe_right uu____3638 FStar_List.unzip  in
        (match uu____3621 with
         | (vars,args) ->
             let vars1 = FStar_List.flatten vars  in
             let uu____3758 =
               let uu____3759 =
                 let uu____3760 =
                   let uu____3775 = FStar_Syntax_Syntax.fv_to_tm fv  in
                   (uu____3775, args)  in
                 FStar_Syntax_Syntax.Tm_app uu____3760  in
               mk1 uu____3759  in
             (vars1, uu____3758))
    | FStar_Syntax_Syntax.Pat_dot_term (x,e) -> ([], e)
  
let (comp_univ_opt :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (uu____3811,uopt) -> uopt
    | FStar_Syntax_Syntax.GTotal (uu____3821,uopt) -> uopt
    | FStar_Syntax_Syntax.Comp c1 ->
        (match c1.FStar_Syntax_Syntax.comp_univs with
         | [] -> FStar_Pervasives_Native.None
         | hd1::uu____3835 -> FStar_Pervasives_Native.Some hd1)
  
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe,FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.typ)
      FStar_Pervasives_Native.tuple3)
  =
  fun c  ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp,uu____3857)::[] -> wp
      | uu____3874 ->
          let uu____3883 =
            let uu____3884 =
              let uu____3885 =
                FStar_List.map
                  (fun uu____3895  ->
                     match uu____3895 with
                     | (x,uu____3901) -> FStar_Syntax_Print.term_to_string x)
                  c.FStar_Syntax_Syntax.effect_args
                 in
              FStar_All.pipe_right uu____3885 (FStar_String.concat ", ")  in
            FStar_Util.format2
              "Impossible: Got a computation %s with effect args [%s]"
              (c.FStar_Syntax_Syntax.effect_name).FStar_Ident.str uu____3884
             in
          failwith uu____3883
       in
    let uu____3904 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs  in
    (uu____3904, (c.FStar_Syntax_Syntax.result_typ), wp)
  
let (lift_comp :
  FStar_Syntax_Syntax.comp_typ ->
    FStar_Ident.lident ->
      FStar_TypeChecker_Env.mlift -> FStar_Syntax_Syntax.comp_typ)
  =
  fun c  ->
    fun m  ->
      fun lift  ->
        let uu____3920 = destruct_comp c  in
        match uu____3920 with
        | (u,uu____3928,wp) ->
            let uu____3930 =
              let uu____3939 =
                let uu____3946 =
                  lift.FStar_TypeChecker_Env.mlift_wp u
                    c.FStar_Syntax_Syntax.result_typ wp
                   in
                FStar_Syntax_Syntax.as_arg uu____3946  in
              [uu____3939]  in
            {
              FStar_Syntax_Syntax.comp_univs = [u];
              FStar_Syntax_Syntax.effect_name = m;
              FStar_Syntax_Syntax.result_typ =
                (c.FStar_Syntax_Syntax.result_typ);
              FStar_Syntax_Syntax.effect_args = uu____3930;
              FStar_Syntax_Syntax.flags = []
            }
  
let (join_effects :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> FStar_Ident.lident -> FStar_Ident.lident)
  =
  fun env  ->
    fun l1  ->
      fun l2  ->
        let uu____3974 =
          let uu____3981 = FStar_TypeChecker_Env.norm_eff_name env l1  in
          let uu____3982 = FStar_TypeChecker_Env.norm_eff_name env l2  in
          FStar_TypeChecker_Env.join env uu____3981 uu____3982  in
        match uu____3974 with | (m,uu____3984,uu____3985) -> m
  
let (join_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_Syntax_Syntax.lcomp -> FStar_Ident.lident)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let uu____4001 =
          (FStar_Syntax_Util.is_total_lcomp c1) &&
            (FStar_Syntax_Util.is_total_lcomp c2)
           in
        if uu____4001
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
        let uu____4044 =
          FStar_TypeChecker_Env.join env c11.FStar_Syntax_Syntax.effect_name
            c21.FStar_Syntax_Syntax.effect_name
           in
        match uu____4044 with
        | (m,lift1,lift2) ->
            let m1 = lift_comp c11 m lift1  in
            let m2 = lift_comp c21 m lift2  in
            let md = FStar_TypeChecker_Env.get_effect_decl env m  in
            let uu____4081 =
              FStar_TypeChecker_Env.wp_signature env
                md.FStar_Syntax_Syntax.mname
               in
            (match uu____4081 with
             | (a,kwp) ->
                 let uu____4112 = destruct_comp m1  in
                 let uu____4119 = destruct_comp m2  in
                 ((md, a, kwp), uu____4112, uu____4119))
  
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
            let uu____4199 =
              let uu____4200 =
                let uu____4209 = FStar_Syntax_Syntax.as_arg wp  in
                [uu____4209]  in
              {
                FStar_Syntax_Syntax.comp_univs = [u_result];
                FStar_Syntax_Syntax.effect_name = mname;
                FStar_Syntax_Syntax.result_typ = result;
                FStar_Syntax_Syntax.effect_args = uu____4200;
                FStar_Syntax_Syntax.flags = flags1
              }  in
            FStar_Syntax_Syntax.mk_Comp uu____4199
  
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
          let uu____4285 =
            FStar_Ident.lid_equals mname FStar_Parser_Const.effect_Tot_lid
             in
          if uu____4285
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
      let uu____4297 =
        FStar_Syntax_Subst.subst subst1 lc.FStar_Syntax_Syntax.res_typ  in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name uu____4297
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____4300  ->
           let uu____4301 = FStar_Syntax_Syntax.lcomp_comp lc  in
           FStar_Syntax_Subst.subst_comp subst1 uu____4301)
  
let (is_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4307 =
      let uu____4308 = FStar_Syntax_Subst.compress t  in
      uu____4308.FStar_Syntax_Syntax.n  in
    match uu____4307 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4311 -> true
    | uu____4324 -> false
  
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
              let uu____4381 =
                let uu____4382 = FStar_TypeChecker_Env.should_verify env  in
                FStar_All.pipe_left Prims.op_Negation uu____4382  in
              if uu____4381
              then f
              else (let uu____4384 = reason1 ()  in label uu____4384 r f)
  
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
            let uu___128_4401 = g  in
            let uu____4402 =
              let uu____4403 = label reason r f  in
              FStar_TypeChecker_Common.NonTrivial uu____4403  in
            {
              FStar_TypeChecker_Env.guard_f = uu____4402;
              FStar_TypeChecker_Env.deferred =
                (uu___128_4401.FStar_TypeChecker_Env.deferred);
              FStar_TypeChecker_Env.univ_ineqs =
                (uu___128_4401.FStar_TypeChecker_Env.univ_ineqs);
              FStar_TypeChecker_Env.implicits =
                (uu___128_4401.FStar_TypeChecker_Env.implicits)
            }
  
let (close_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv Prims.list ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun bvs  ->
      fun c  ->
        let uu____4423 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4423
        then c
        else
          (let uu____4425 =
             env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
           if uu____4425
           then c
           else
             (let close_wp u_res md res_t bvs1 wp0 =
                FStar_List.fold_right
                  (fun x  ->
                     fun wp  ->
                       let bs =
                         let uu____4484 = FStar_Syntax_Syntax.mk_binder x  in
                         [uu____4484]  in
                       let us =
                         let uu____4500 =
                           let uu____4503 =
                             env.FStar_TypeChecker_Env.universe_of env
                               x.FStar_Syntax_Syntax.sort
                              in
                           [uu____4503]  in
                         u_res :: uu____4500  in
                       let wp1 =
                         FStar_Syntax_Util.abs bs wp
                           (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.mk_residual_comp
                                 FStar_Parser_Const.effect_Tot_lid
                                 FStar_Pervasives_Native.None
                                 [FStar_Syntax_Syntax.TOTAL]))
                          in
                       let uu____4509 =
                         let uu____4514 =
                           FStar_TypeChecker_Env.inst_effect_fun_with us env
                             md md.FStar_Syntax_Syntax.close_wp
                            in
                         let uu____4515 =
                           let uu____4516 = FStar_Syntax_Syntax.as_arg res_t
                              in
                           let uu____4523 =
                             let uu____4532 =
                               FStar_Syntax_Syntax.as_arg
                                 x.FStar_Syntax_Syntax.sort
                                in
                             let uu____4539 =
                               let uu____4548 =
                                 FStar_Syntax_Syntax.as_arg wp1  in
                               [uu____4548]  in
                             uu____4532 :: uu____4539  in
                           uu____4516 :: uu____4523  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____4514 uu____4515
                          in
                       uu____4509 FStar_Pervasives_Native.None
                         wp0.FStar_Syntax_Syntax.pos) bvs1 wp0
                 in
              let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
              let uu____4582 = destruct_comp c1  in
              match uu____4582 with
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
          (fun uu____4617  ->
             let uu____4618 = FStar_Syntax_Syntax.lcomp_comp lc  in
             close_comp env bvs uu____4618)
  
let (should_not_inline_lc : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___100_4627  ->
            match uu___100_4627 with
            | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
            | uu____4628 -> false))
  
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
                (let uu____4650 =
                   FStar_Syntax_Util.is_unit lc.FStar_Syntax_Syntax.res_typ
                    in
                 Prims.op_Negation uu____4650))
               &&
               (let uu____4657 = FStar_Syntax_Util.head_and_args' e  in
                match uu____4657 with
                | (head1,uu____4671) ->
                    let uu____4688 =
                      let uu____4689 = FStar_Syntax_Util.un_uinst head1  in
                      uu____4689.FStar_Syntax_Syntax.n  in
                    (match uu____4688 with
                     | FStar_Syntax_Syntax.Tm_fvar fv ->
                         let uu____4693 =
                           let uu____4694 = FStar_Syntax_Syntax.lid_of_fv fv
                              in
                           FStar_TypeChecker_Env.is_irreducible env
                             uu____4694
                            in
                         Prims.op_Negation uu____4693
                     | uu____4695 -> true)))
              &&
              (let uu____4697 = should_not_inline_lc lc  in
               Prims.op_Negation uu____4697)
  
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
            let uu____4731 =
              let uu____4732 =
                FStar_TypeChecker_Env.lid_exists env
                  FStar_Parser_Const.effect_GTot_lid
                 in
              FStar_All.pipe_left Prims.op_Negation uu____4732  in
            if uu____4731
            then FStar_Syntax_Syntax.mk_Total t
            else
              (let uu____4734 = FStar_Syntax_Util.is_unit t  in
               if uu____4734
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
                    let uu____4740 =
                      env.FStar_TypeChecker_Env.lax &&
                        (FStar_Options.ml_ish ())
                       in
                    if uu____4740
                    then FStar_Syntax_Syntax.tun
                    else
                      (let uu____4742 =
                         FStar_TypeChecker_Env.wp_signature env
                           FStar_Parser_Const.effect_PURE_lid
                          in
                       match uu____4742 with
                       | (a,kwp) ->
                           let k =
                             FStar_Syntax_Subst.subst
                               [FStar_Syntax_Syntax.NT (a, t)] kwp
                              in
                           let uu____4752 =
                             let uu____4753 =
                               let uu____4758 =
                                 FStar_TypeChecker_Env.inst_effect_fun_with
                                   [u_t] env m m.FStar_Syntax_Syntax.ret_wp
                                  in
                               let uu____4759 =
                                 let uu____4760 =
                                   FStar_Syntax_Syntax.as_arg t  in
                                 let uu____4767 =
                                   let uu____4776 =
                                     FStar_Syntax_Syntax.as_arg v1  in
                                   [uu____4776]  in
                                 uu____4760 :: uu____4767  in
                               FStar_Syntax_Syntax.mk_Tm_app uu____4758
                                 uu____4759
                                in
                             uu____4753 FStar_Pervasives_Native.None
                               v1.FStar_Syntax_Syntax.pos
                              in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Normalize.Beta;
                             FStar_TypeChecker_Normalize.NoFullNorm] env
                             uu____4752)
                     in
                  mk_comp m u_t t wp [FStar_Syntax_Syntax.RETURN]))
             in
          (let uu____4804 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Return")
              in
           if uu____4804
           then
             let uu____4805 =
               FStar_Range.string_of_range v1.FStar_Syntax_Syntax.pos  in
             let uu____4806 = FStar_Syntax_Print.term_to_string v1  in
             let uu____4807 =
               FStar_TypeChecker_Normalize.comp_to_string env c  in
             FStar_Util.print3 "(%s) returning %s at comp type %s\n"
               uu____4805 uu____4806 uu____4807
           else ());
          c
  
let (weaken_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list)
  =
  fun flags1  ->
    let uu____4820 =
      FStar_All.pipe_right flags1
        (FStar_Util.for_some
           (fun uu___101_4824  ->
              match uu___101_4824 with
              | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  -> true
              | uu____4825 -> false))
       in
    if uu____4820
    then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
    else
      FStar_All.pipe_right flags1
        (FStar_List.collect
           (fun uu___102_4834  ->
              match uu___102_4834 with
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
        let uu____4853 = FStar_Syntax_Util.is_ml_comp c  in
        if uu____4853
        then c
        else
          (let c1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
           let uu____4856 = destruct_comp c1  in
           match uu____4856 with
           | (u_res_t,res_t,wp) ->
               let md =
                 FStar_TypeChecker_Env.get_effect_decl env
                   c1.FStar_Syntax_Syntax.effect_name
                  in
               let wp1 =
                 let uu____4870 =
                   let uu____4875 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t] env
                       md md.FStar_Syntax_Syntax.assume_p
                      in
                   let uu____4876 =
                     let uu____4877 = FStar_Syntax_Syntax.as_arg res_t  in
                     let uu____4884 =
                       let uu____4893 = FStar_Syntax_Syntax.as_arg formula
                          in
                       let uu____4900 =
                         let uu____4909 = FStar_Syntax_Syntax.as_arg wp  in
                         [uu____4909]  in
                       uu____4893 :: uu____4900  in
                     uu____4877 :: uu____4884  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____4875 uu____4876  in
                 uu____4870 FStar_Pervasives_Native.None
                   wp.FStar_Syntax_Syntax.pos
                  in
               let uu____4942 = weaken_flags c1.FStar_Syntax_Syntax.flags  in
               mk_comp md u_res_t res_t wp1 uu____4942)
  
let (weaken_precondition :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp ->
      FStar_TypeChecker_Common.guard_formula -> FStar_Syntax_Syntax.lcomp)
  =
  fun env  ->
    fun lc  ->
      fun f  ->
        let weaken uu____4965 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let uu____4967 =
            env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())  in
          if uu____4967
          then c
          else
            (match f with
             | FStar_TypeChecker_Common.Trivial  -> c
             | FStar_TypeChecker_Common.NonTrivial f1 -> weaken_comp env c f1)
           in
        let uu____4970 = weaken_flags lc.FStar_Syntax_Syntax.cflags  in
        FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
          lc.FStar_Syntax_Syntax.res_typ uu____4970 weaken
  
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
               let uu____5013 = destruct_comp c1  in
               match uu____5013 with
               | (u_res_t,res_t,wp) ->
                   let md =
                     FStar_TypeChecker_Env.get_effect_decl env
                       c1.FStar_Syntax_Syntax.effect_name
                      in
                   let wp1 =
                     let uu____5027 =
                       let uu____5032 =
                         FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                           env md md.FStar_Syntax_Syntax.assert_p
                          in
                       let uu____5033 =
                         let uu____5034 = FStar_Syntax_Syntax.as_arg res_t
                            in
                         let uu____5041 =
                           let uu____5050 =
                             let uu____5057 =
                               let uu____5058 =
                                 FStar_TypeChecker_Env.get_range env  in
                               label_opt env reason uu____5058 f  in
                             FStar_All.pipe_left FStar_Syntax_Syntax.as_arg
                               uu____5057
                              in
                           let uu____5065 =
                             let uu____5074 = FStar_Syntax_Syntax.as_arg wp
                                in
                             [uu____5074]  in
                           uu____5050 :: uu____5065  in
                         uu____5034 :: uu____5041  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____5032 uu____5033
                        in
                     uu____5027 FStar_Pervasives_Native.None
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
            let uu____5149 =
              FStar_TypeChecker_Rel.is_trivial_guard_formula g0  in
            if uu____5149
            then (lc, g0)
            else
              (let flags1 =
                 let uu____5158 =
                   let uu____5165 = FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
                      in
                   if uu____5165
                   then (true, [FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION])
                   else (false, [])  in
                 match uu____5158 with
                 | (maybe_trivial_post,flags1) ->
                     let uu____5185 =
                       FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                         (FStar_List.collect
                            (fun uu___103_5193  ->
                               match uu___103_5193 with
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
                               | uu____5196 -> []))
                        in
                     FStar_List.append flags1 uu____5185
                  in
               let strengthen uu____5202 =
                 let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                 if env.FStar_TypeChecker_Env.lax
                 then c
                 else
                   (let g01 = FStar_TypeChecker_Rel.simplify_guard env g0  in
                    let uu____5206 = FStar_TypeChecker_Rel.guard_form g01  in
                    match uu____5206 with
                    | FStar_TypeChecker_Common.Trivial  -> c
                    | FStar_TypeChecker_Common.NonTrivial f ->
                        ((let uu____5209 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              FStar_Options.Extreme
                             in
                          if uu____5209
                          then
                            let uu____5210 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                e_for_debug_only
                               in
                            let uu____5211 =
                              FStar_TypeChecker_Normalize.term_to_string env
                                f
                               in
                            FStar_Util.print2
                              "-------------Strengthening pre-condition of term %s with guard %s\n"
                              uu____5210 uu____5211
                          else ());
                         strengthen_comp env reason c f flags1))
                  in
               let uu____5213 =
                 let uu____5214 =
                   FStar_TypeChecker_Env.norm_eff_name env
                     lc.FStar_Syntax_Syntax.eff_name
                    in
                 FStar_Syntax_Syntax.mk_lcomp uu____5214
                   lc.FStar_Syntax_Syntax.res_typ flags1 strengthen
                  in
               (uu____5213,
                 (let uu___129_5216 = g0  in
                  {
                    FStar_TypeChecker_Env.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Env.deferred =
                      (uu___129_5216.FStar_TypeChecker_Env.deferred);
                    FStar_TypeChecker_Env.univ_ineqs =
                      (uu___129_5216.FStar_TypeChecker_Env.univ_ineqs);
                    FStar_TypeChecker_Env.implicits =
                      (uu___129_5216.FStar_TypeChecker_Env.implicits)
                  })))
  
let (lcomp_has_trivial_postcondition :
  FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc) ||
      (FStar_Util.for_some
         (fun uu___104_5223  ->
            match uu___104_5223 with
            | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
            | FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION  -> true
            | uu____5224 -> false) lc.FStar_Syntax_Syntax.cflags)
  
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
          let uu____5251 =
            (FStar_Syntax_Util.is_lcomp_partial_return lc) ||
              env.FStar_TypeChecker_Env.lax
             in
          if uu____5251
          then e
          else
            (let uu____5255 =
               (lcomp_has_trivial_postcondition lc) &&
                 (let uu____5257 =
                    FStar_TypeChecker_Env.try_lookup_lid env
                      FStar_Parser_Const.with_type_lid
                     in
                  FStar_Option.isSome uu____5257)
                in
             if uu____5255
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
          fun uu____5307  ->
            match uu____5307 with
            | (b,lc2) ->
                let debug1 f =
                  let uu____5327 =
                    (FStar_TypeChecker_Env.debug env FStar_Options.Extreme)
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "bind"))
                     in
                  if uu____5327 then f () else ()  in
                let lc11 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc1  in
                let lc21 =
                  FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env lc2  in
                let joined_eff = join_lcomp env lc11 lc21  in
                let bind_flags =
                  let uu____5335 =
                    (should_not_inline_lc lc11) ||
                      (should_not_inline_lc lc21)
                     in
                  if uu____5335
                  then [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                  else
                    (let flags1 =
                       let uu____5342 = FStar_Syntax_Util.is_total_lcomp lc11
                          in
                       if uu____5342
                       then
                         let uu____5345 =
                           FStar_Syntax_Util.is_total_lcomp lc21  in
                         (if uu____5345
                          then [FStar_Syntax_Syntax.TOTAL]
                          else
                            (let uu____5349 =
                               FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21
                                in
                             if uu____5349
                             then [FStar_Syntax_Syntax.SOMETRIVIAL]
                             else []))
                       else
                         (let uu____5354 =
                            (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc11) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_lcomp lc21)
                             in
                          if uu____5354
                          then [FStar_Syntax_Syntax.SOMETRIVIAL]
                          else [])
                        in
                     let uu____5358 = lcomp_has_trivial_postcondition lc21
                        in
                     if uu____5358
                     then FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION :: flags1
                     else flags1)
                   in
                let bind_it uu____5367 =
                  let uu____5368 =
                    env.FStar_TypeChecker_Env.lax &&
                      (FStar_Options.ml_ish ())
                     in
                  if uu____5368
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
                       (fun uu____5382  ->
                          let uu____5383 =
                            FStar_Syntax_Print.comp_to_string c1  in
                          let uu____5384 =
                            match b with
                            | FStar_Pervasives_Native.None  -> "none"
                            | FStar_Pervasives_Native.Some x ->
                                FStar_Syntax_Print.bv_to_string x
                             in
                          let uu____5386 =
                            FStar_Syntax_Print.comp_to_string c2  in
                          FStar_Util.print3
                            "(1) bind: \n\tc1=%s\n\tx=%s\n\tc2=%s\n(1. end bind)\n"
                            uu____5383 uu____5384 uu____5386);
                     (let aux uu____5400 =
                        let uu____5401 = FStar_Syntax_Util.is_trivial_wp c1
                           in
                        if uu____5401
                        then
                          match b with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Util.Inl (c2, "trivial no binder")
                          | FStar_Pervasives_Native.Some uu____5422 ->
                              let uu____5423 =
                                FStar_Syntax_Util.is_ml_comp c2  in
                              (if uu____5423
                               then FStar_Util.Inl (c2, "trivial ml")
                               else
                                 FStar_Util.Inr
                                   "c1 trivial; but c2 is not ML")
                        else
                          (let uu____5442 =
                             (FStar_Syntax_Util.is_ml_comp c1) &&
                               (FStar_Syntax_Util.is_ml_comp c2)
                              in
                           if uu____5442
                           then FStar_Util.Inl (c2, "both ml")
                           else
                             FStar_Util.Inr
                               "c1 not trivial, and both are not ML")
                         in
                      let subst_c2 e1opt1 reason =
                        match (e1opt1, b) with
                        | (FStar_Pervasives_Native.Some
                           e,FStar_Pervasives_Native.Some x) ->
                            let uu____5513 =
                              let uu____5518 =
                                FStar_Syntax_Subst.subst_comp
                                  [FStar_Syntax_Syntax.NT (x, e)] c2
                                 in
                              (uu____5518, reason)  in
                            FStar_Util.Inl uu____5513
                        | uu____5525 -> aux ()  in
                      let try_simplify uu____5549 =
                        let rec maybe_close t x c =
                          let uu____5566 =
                            let uu____5567 =
                              FStar_TypeChecker_Normalize.unfold_whnf env t
                               in
                            uu____5567.FStar_Syntax_Syntax.n  in
                          match uu____5566 with
                          | FStar_Syntax_Syntax.Tm_refine (y,uu____5571) ->
                              maybe_close y.FStar_Syntax_Syntax.sort x c
                          | FStar_Syntax_Syntax.Tm_fvar fv when
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.unit_lid
                              -> close_comp env [x] c
                          | uu____5577 -> c  in
                        let uu____5578 =
                          let uu____5579 =
                            FStar_TypeChecker_Env.try_lookup_effect_lid env
                              FStar_Parser_Const.effect_GTot_lid
                             in
                          FStar_Option.isNone uu____5579  in
                        if uu____5578
                        then
                          let uu____5590 =
                            (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                              (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                             in
                          (if uu____5590
                           then
                             FStar_Util.Inl
                               (c2, "Early in prims; we don't have bind yet")
                           else
                             (let uu____5604 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Errors.raise_error
                                (FStar_Errors.Fatal_NonTrivialPreConditionInPrims,
                                  "Non-trivial pre-conditions very early in prims, even before we have defined the PURE monad")
                                uu____5604))
                        else
                          (let uu____5614 =
                             (FStar_Syntax_Util.is_total_comp c1) &&
                               (FStar_Syntax_Util.is_total_comp c2)
                              in
                           if uu____5614
                           then subst_c2 e1opt "both total"
                           else
                             (let uu____5624 =
                                (FStar_Syntax_Util.is_tot_or_gtot_comp c1) &&
                                  (FStar_Syntax_Util.is_tot_or_gtot_comp c2)
                                 in
                              if uu____5624
                              then
                                let uu____5633 =
                                  let uu____5638 =
                                    FStar_Syntax_Syntax.mk_GTotal
                                      (FStar_Syntax_Util.comp_result c2)
                                     in
                                  (uu____5638, "both gtot")  in
                                FStar_Util.Inl uu____5633
                              else
                                (match (e1opt, b) with
                                 | (FStar_Pervasives_Native.Some
                                    e,FStar_Pervasives_Native.Some x) ->
                                     let uu____5662 =
                                       (FStar_Syntax_Util.is_total_comp c1)
                                         &&
                                         (let uu____5664 =
                                            FStar_Syntax_Syntax.is_null_bv x
                                             in
                                          Prims.op_Negation uu____5664)
                                        in
                                     if uu____5662
                                     then
                                       let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e)] c2
                                          in
                                       let x1 =
                                         let uu___130_5677 = x  in
                                         {
                                           FStar_Syntax_Syntax.ppname =
                                             (uu___130_5677.FStar_Syntax_Syntax.ppname);
                                           FStar_Syntax_Syntax.index =
                                             (uu___130_5677.FStar_Syntax_Syntax.index);
                                           FStar_Syntax_Syntax.sort =
                                             (FStar_Syntax_Util.comp_result
                                                c1)
                                         }  in
                                       let uu____5678 =
                                         let uu____5683 =
                                           maybe_close
                                             x1.FStar_Syntax_Syntax.sort x1
                                             c21
                                            in
                                         (uu____5683, "c1 Tot")  in
                                       FStar_Util.Inl uu____5678
                                     else aux ()
                                 | uu____5689 -> aux ())))
                         in
                      let uu____5698 = try_simplify ()  in
                      match uu____5698 with
                      | FStar_Util.Inl (c,reason) ->
                          (debug1
                             (fun uu____5718  ->
                                let uu____5719 =
                                  FStar_Syntax_Print.comp_to_string c  in
                                FStar_Util.print2
                                  "(2) bind: Simplified (because %s) to\n\t%s\n"
                                  reason uu____5719);
                           c)
                      | FStar_Util.Inr reason ->
                          (debug1
                             (fun uu____5728  ->
                                FStar_Util.print1
                                  "(2) bind: Not simplified because %s\n"
                                  reason);
                           (let mk_bind c11 b1 c21 =
                              let uu____5749 = lift_and_destruct env c11 c21
                                 in
                              match uu____5749 with
                              | ((md,a,kwp),(u_t1,t1,wp1),(u_t2,t2,wp2)) ->
                                  let bs =
                                    match b1 with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____5802 =
                                          FStar_Syntax_Syntax.null_binder t1
                                           in
                                        [uu____5802]
                                    | FStar_Pervasives_Native.Some x ->
                                        let uu____5816 =
                                          FStar_Syntax_Syntax.mk_binder x  in
                                        [uu____5816]
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
                                    let uu____5843 =
                                      FStar_Syntax_Syntax.as_arg r11  in
                                    let uu____5850 =
                                      let uu____5859 =
                                        FStar_Syntax_Syntax.as_arg t1  in
                                      let uu____5866 =
                                        let uu____5875 =
                                          FStar_Syntax_Syntax.as_arg t2  in
                                        let uu____5882 =
                                          let uu____5891 =
                                            FStar_Syntax_Syntax.as_arg wp1
                                             in
                                          let uu____5898 =
                                            let uu____5907 =
                                              let uu____5914 = mk_lam wp2  in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____5914
                                               in
                                            [uu____5907]  in
                                          uu____5891 :: uu____5898  in
                                        uu____5875 :: uu____5882  in
                                      uu____5859 :: uu____5866  in
                                    uu____5843 :: uu____5850  in
                                  let wp =
                                    let uu____5954 =
                                      let uu____5959 =
                                        FStar_TypeChecker_Env.inst_effect_fun_with
                                          [u_t1; u_t2] env md
                                          md.FStar_Syntax_Syntax.bind_wp
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____5959 wp_args
                                       in
                                    uu____5954 FStar_Pervasives_Native.None
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
                              let uu____5984 =
                                FStar_TypeChecker_Env.join env
                                  c12.FStar_Syntax_Syntax.effect_name
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              match uu____5984 with
                              | (m,uu____5992,lift2) ->
                                  let c23 =
                                    let uu____5995 = lift_comp c22 m lift2
                                       in
                                    FStar_Syntax_Syntax.mk_Comp uu____5995
                                     in
                                  let uu____5996 = destruct_comp c12  in
                                  (match uu____5996 with
                                   | (u1,t1,wp1) ->
                                       let md_pure_or_ghost =
                                         FStar_TypeChecker_Env.get_effect_decl
                                           env
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let vc1 =
                                         let uu____6010 =
                                           let uu____6015 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [u1] env md_pure_or_ghost
                                               md_pure_or_ghost.FStar_Syntax_Syntax.trivial
                                              in
                                           let uu____6016 =
                                             let uu____6017 =
                                               FStar_Syntax_Syntax.as_arg t1
                                                in
                                             let uu____6024 =
                                               let uu____6033 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wp1
                                                  in
                                               [uu____6033]  in
                                             uu____6017 :: uu____6024  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____6015 uu____6016
                                            in
                                         uu____6010
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
                            let uu____6064 = destruct_comp c1_typ  in
                            match uu____6064 with
                            | (u_res_t1,res_t1,uu____6073) ->
                                let uu____6074 =
                                  (FStar_Option.isSome b) &&
                                    (should_return env e1opt lc11)
                                   in
                                if uu____6074
                                then
                                  let e1 = FStar_Option.get e1opt  in
                                  let x = FStar_Option.get b  in
                                  let uu____6077 =
                                    FStar_Syntax_Util.is_partial_return c1
                                     in
                                  (if uu____6077
                                   then
                                     (debug1
                                        (fun uu____6085  ->
                                           let uu____6086 =
                                             FStar_TypeChecker_Normalize.term_to_string
                                               env e1
                                              in
                                           let uu____6087 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           FStar_Util.print2
                                             "(3) bind (case a): Substituting %s for %s"
                                             uu____6086 uu____6087);
                                      (let c21 =
                                         FStar_Syntax_Subst.subst_comp
                                           [FStar_Syntax_Syntax.NT (x, e1)]
                                           c2
                                          in
                                       mk_bind c1 b c21))
                                   else
                                     (let uu____6092 =
                                        ((FStar_Options.vcgen_optimize_bind_as_seq
                                            ())
                                           &&
                                           (lcomp_has_trivial_postcondition
                                              lc11))
                                          &&
                                          (let uu____6094 =
                                             FStar_TypeChecker_Env.try_lookup_lid
                                               env
                                               FStar_Parser_Const.with_type_lid
                                              in
                                           FStar_Option.isSome uu____6094)
                                         in
                                      if uu____6092
                                      then
                                        let e1' =
                                          let uu____6114 =
                                            FStar_Options.vcgen_decorate_with_type
                                              ()
                                             in
                                          if uu____6114
                                          then
                                            FStar_Syntax_Util.mk_with_type
                                              u_res_t1 res_t1 e1
                                          else e1  in
                                        (debug1
                                           (fun uu____6123  ->
                                              let uu____6124 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1'
                                                 in
                                              let uu____6125 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case b): Substituting %s for %s"
                                                uu____6124 uu____6125);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT
                                                 (x, e1')] c2
                                             in
                                          mk_seq c1 b c21))
                                      else
                                        (debug1
                                           (fun uu____6137  ->
                                              let uu____6138 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env e1
                                                 in
                                              let uu____6139 =
                                                FStar_Syntax_Print.bv_to_string
                                                  x
                                                 in
                                              FStar_Util.print2
                                                "(3) bind (case c): Adding equality %s = %s"
                                                uu____6138 uu____6139);
                                         (let c21 =
                                            FStar_Syntax_Subst.subst_comp
                                              [FStar_Syntax_Syntax.NT (x, e1)]
                                              c2
                                             in
                                          let x_eq_e =
                                            let uu____6144 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                x
                                               in
                                            FStar_Syntax_Util.mk_eq2 u_res_t1
                                              res_t1 e1 uu____6144
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
      | uu____6160 -> g2
  
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
            (let uu____6182 = FStar_Syntax_Util.is_lcomp_partial_return lc
                in
             Prims.op_Negation uu____6182)
           in
        let flags1 =
          if should_return1
          then
            let uu____6188 = FStar_Syntax_Util.is_total_lcomp lc  in
            (if uu____6188
             then FStar_Syntax_Syntax.RETURN ::
               (lc.FStar_Syntax_Syntax.cflags)
             else FStar_Syntax_Syntax.PARTIAL_RETURN ::
               (lc.FStar_Syntax_Syntax.cflags))
          else lc.FStar_Syntax_Syntax.cflags  in
        let refine1 uu____6200 =
          let c = FStar_Syntax_Syntax.lcomp_comp lc  in
          let u_t =
            match comp_univ_opt c with
            | FStar_Pervasives_Native.Some u_t -> u_t
            | FStar_Pervasives_Native.None  ->
                env.FStar_TypeChecker_Env.universe_of env
                  (FStar_Syntax_Util.comp_result c)
             in
          let uu____6204 = FStar_Syntax_Util.is_tot_or_gtot_comp c  in
          if uu____6204
          then
            let retc =
              return_value env (FStar_Pervasives_Native.Some u_t)
                (FStar_Syntax_Util.comp_result c) e
               in
            let uu____6208 =
              let uu____6209 = FStar_Syntax_Util.is_pure_comp c  in
              Prims.op_Negation uu____6209  in
            (if uu____6208
             then
               let retc1 = FStar_Syntax_Util.comp_to_comp_typ retc  in
               let retc2 =
                 let uu___131_6214 = retc1  in
                 {
                   FStar_Syntax_Syntax.comp_univs =
                     (uu___131_6214.FStar_Syntax_Syntax.comp_univs);
                   FStar_Syntax_Syntax.effect_name =
                     FStar_Parser_Const.effect_GHOST_lid;
                   FStar_Syntax_Syntax.result_typ =
                     (uu___131_6214.FStar_Syntax_Syntax.result_typ);
                   FStar_Syntax_Syntax.effect_args =
                     (uu___131_6214.FStar_Syntax_Syntax.effect_args);
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
               let uu____6225 =
                 let uu____6226 =
                   return_value env (FStar_Pervasives_Native.Some u_t) t xexp
                    in
                 FStar_Syntax_Util.comp_set_flags uu____6226
                   [FStar_Syntax_Syntax.PARTIAL_RETURN]
                  in
               FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____6225
                in
             let eq1 = FStar_Syntax_Util.mk_eq2 u_t t xexp e  in
             let eq_ret =
               weaken_precondition env ret1
                 (FStar_TypeChecker_Common.NonTrivial eq1)
                in
             let uu____6229 =
               let uu____6230 =
                 let uu____6231 = FStar_Syntax_Util.lcomp_of_comp c2  in
                 bind e.FStar_Syntax_Syntax.pos env
                   FStar_Pervasives_Native.None uu____6231
                   ((FStar_Pervasives_Native.Some x), eq_ret)
                  in
               FStar_Syntax_Syntax.lcomp_comp uu____6230  in
             FStar_Syntax_Util.comp_set_flags uu____6229 flags1)
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
            fun uu____6266  ->
              match uu____6266 with
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
                    let uu____6278 =
                      ((let uu____6281 = is_pure_or_ghost_effect env eff1  in
                        Prims.op_Negation uu____6281) ||
                         (should_not_inline_lc lc1))
                        && (is_pure_or_ghost_effect env eff2)
                       in
                    if uu____6278
                    then maybe_assume_result_eq_pure_term env e2 lc2
                    else lc2  in
                  bind r env e1opt lc1 (x, lc21)
  
let (fvar_const :
  FStar_TypeChecker_Env.env -> FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun lid  ->
      let uu____6295 =
        let uu____6296 = FStar_TypeChecker_Env.get_range env  in
        FStar_Ident.set_lid_range lid uu____6296  in
      FStar_Syntax_Syntax.fvar uu____6295 FStar_Syntax_Syntax.delta_constant
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
               fun uu____6362  ->
                 match uu____6362 with
                 | (uu____6375,eff_label,uu____6377,uu____6378) ->
                     join_effects env eff eff_label)
            FStar_Parser_Const.effect_PURE_lid lcases
           in
        let uu____6389 =
          let uu____6396 =
            FStar_All.pipe_right lcases
              (FStar_Util.for_some
                 (fun uu____6430  ->
                    match uu____6430 with
                    | (uu____6443,uu____6444,flags1,uu____6446) ->
                        FStar_All.pipe_right flags1
                          (FStar_Util.for_some
                             (fun uu___105_6460  ->
                                match uu___105_6460 with
                                | FStar_Syntax_Syntax.SHOULD_NOT_INLINE  ->
                                    true
                                | uu____6461 -> false))))
             in
          if uu____6396
          then (true, [FStar_Syntax_Syntax.SHOULD_NOT_INLINE])
          else (false, [])  in
        match uu____6389 with
        | (should_not_inline_whole_match,bind_cases_flags) ->
            let bind_cases uu____6484 =
              let u_res_t = env.FStar_TypeChecker_Env.universe_of env res_t
                 in
              let uu____6486 =
                env.FStar_TypeChecker_Env.lax && (FStar_Options.ml_ish ())
                 in
              if uu____6486
              then lax_mk_tot_or_comp_l eff u_res_t res_t []
              else
                (let ifthenelse md res_t1 g wp_t wp_e =
                   let uu____6524 =
                     FStar_Range.union_ranges wp_t.FStar_Syntax_Syntax.pos
                       wp_e.FStar_Syntax_Syntax.pos
                      in
                   let uu____6525 =
                     let uu____6530 =
                       FStar_TypeChecker_Env.inst_effect_fun_with [u_res_t]
                         env md md.FStar_Syntax_Syntax.if_then_else
                        in
                     let uu____6531 =
                       let uu____6532 = FStar_Syntax_Syntax.as_arg res_t1  in
                       let uu____6539 =
                         let uu____6548 = FStar_Syntax_Syntax.as_arg g  in
                         let uu____6555 =
                           let uu____6564 = FStar_Syntax_Syntax.as_arg wp_t
                              in
                           let uu____6571 =
                             let uu____6580 = FStar_Syntax_Syntax.as_arg wp_e
                                in
                             [uu____6580]  in
                           uu____6564 :: uu____6571  in
                         uu____6548 :: uu____6555  in
                       uu____6532 :: uu____6539  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____6530 uu____6531  in
                   uu____6525 FStar_Pervasives_Native.None uu____6524  in
                 let default_case =
                   let post_k =
                     let uu____6623 =
                       let uu____6630 = FStar_Syntax_Syntax.null_binder res_t
                          in
                       [uu____6630]  in
                     let uu____6643 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6623 uu____6643  in
                   let kwp =
                     let uu____6649 =
                       let uu____6656 =
                         FStar_Syntax_Syntax.null_binder post_k  in
                       [uu____6656]  in
                     let uu____6669 =
                       FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                        in
                     FStar_Syntax_Util.arrow uu____6649 uu____6669  in
                   let post =
                     FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                       post_k
                      in
                   let wp =
                     let uu____6676 =
                       let uu____6677 = FStar_Syntax_Syntax.mk_binder post
                          in
                       [uu____6677]  in
                     let uu____6690 =
                       let uu____6693 =
                         let uu____6700 = FStar_TypeChecker_Env.get_range env
                            in
                         label FStar_TypeChecker_Err.exhaustiveness_check
                           uu____6700
                          in
                       let uu____6701 =
                         fvar_const env FStar_Parser_Const.false_lid  in
                       FStar_All.pipe_left uu____6693 uu____6701  in
                     FStar_Syntax_Util.abs uu____6676 uu____6690
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
                   let uu____6723 =
                     should_not_inline_whole_match ||
                       (let uu____6725 = is_pure_or_ghost_effect env eff  in
                        Prims.op_Negation uu____6725)
                      in
                   if uu____6723 then cthen true else cthen false  in
                 let comp =
                   FStar_List.fold_right
                     (fun uu____6758  ->
                        fun celse  ->
                          match uu____6758 with
                          | (g,eff_label,uu____6774,cthen) ->
                              let uu____6786 =
                                let uu____6811 =
                                  let uu____6812 =
                                    maybe_return eff_label cthen  in
                                  FStar_Syntax_Syntax.lcomp_comp uu____6812
                                   in
                                lift_and_destruct env uu____6811 celse  in
                              (match uu____6786 with
                               | ((md,uu____6814,uu____6815),(uu____6816,uu____6817,wp_then),
                                  (uu____6819,uu____6820,wp_else)) ->
                                   let uu____6840 =
                                     ifthenelse md res_t g wp_then wp_else
                                      in
                                   mk_comp md u_res_t res_t uu____6840 []))
                     lcases default_case
                    in
                 match lcases with
                 | [] -> comp
                 | uu____6854::[] -> comp
                 | uu____6894 ->
                     let comp1 =
                       FStar_TypeChecker_Env.comp_to_comp_typ env comp  in
                     let md =
                       FStar_TypeChecker_Env.get_effect_decl env
                         comp1.FStar_Syntax_Syntax.effect_name
                        in
                     let uu____6912 = destruct_comp comp1  in
                     (match uu____6912 with
                      | (uu____6919,uu____6920,wp) ->
                          let wp1 =
                            let uu____6925 =
                              let uu____6930 =
                                FStar_TypeChecker_Env.inst_effect_fun_with
                                  [u_res_t] env md
                                  md.FStar_Syntax_Syntax.ite_wp
                                 in
                              let uu____6931 =
                                let uu____6932 =
                                  FStar_Syntax_Syntax.as_arg res_t  in
                                let uu____6939 =
                                  let uu____6948 =
                                    FStar_Syntax_Syntax.as_arg wp  in
                                  [uu____6948]  in
                                uu____6932 :: uu____6939  in
                              FStar_Syntax_Syntax.mk_Tm_app uu____6930
                                uu____6931
                               in
                            uu____6925 FStar_Pervasives_Native.None
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
          let uu____7007 = FStar_TypeChecker_Rel.sub_comp env c c'  in
          match uu____7007 with
          | FStar_Pervasives_Native.None  ->
              let uu____7016 =
                FStar_TypeChecker_Err.computed_computation_type_does_not_match_annotation
                  env e c c'
                 in
              let uu____7021 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.raise_error uu____7016 uu____7021
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
            let uu____7064 =
              let uu____7065 = FStar_Syntax_Subst.compress t2  in
              uu____7065.FStar_Syntax_Syntax.n  in
            match uu____7064 with
            | FStar_Syntax_Syntax.Tm_type uu____7068 -> true
            | uu____7069 -> false  in
          let uu____7070 =
            let uu____7071 =
              FStar_Syntax_Util.unrefine lc.FStar_Syntax_Syntax.res_typ  in
            uu____7071.FStar_Syntax_Syntax.n  in
          match uu____7070 with
          | FStar_Syntax_Syntax.Tm_fvar fv when
              (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid)
                && (is_type1 t)
              ->
              let uu____7079 =
                FStar_TypeChecker_Env.lookup_lid env
                  FStar_Parser_Const.b2t_lid
                 in
              let b2t1 =
                let uu____7089 =
                  FStar_Ident.set_lid_range FStar_Parser_Const.b2t_lid
                    e.FStar_Syntax_Syntax.pos
                   in
                FStar_Syntax_Syntax.fvar uu____7089
                  (FStar_Syntax_Syntax.Delta_constant_at_level
                     (Prims.parse_int "1")) FStar_Pervasives_Native.None
                 in
              let lc1 =
                let uu____7091 =
                  let uu____7092 =
                    let uu____7093 =
                      FStar_Syntax_Syntax.mk_Total FStar_Syntax_Util.ktype0
                       in
                    FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp
                      uu____7093
                     in
                  (FStar_Pervasives_Native.None, uu____7092)  in
                bind e.FStar_Syntax_Syntax.pos env
                  (FStar_Pervasives_Native.Some e) lc uu____7091
                 in
              let e1 =
                let uu____7099 =
                  let uu____7104 =
                    let uu____7105 = FStar_Syntax_Syntax.as_arg e  in
                    [uu____7105]  in
                  FStar_Syntax_Syntax.mk_Tm_app b2t1 uu____7104  in
                uu____7099 FStar_Pervasives_Native.None
                  e.FStar_Syntax_Syntax.pos
                 in
              (e1, lc1)
          | uu____7126 -> (e, lc)
  
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
              (let uu____7163 =
                 FStar_TypeChecker_Env.effect_decl_opt env
                   lc.FStar_Syntax_Syntax.eff_name
                  in
               match uu____7163 with
               | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                   FStar_All.pipe_right qualifiers
                     (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               | uu____7186 -> false)
             in
          let gopt =
            if use_eq
            then
              let uu____7208 =
                FStar_TypeChecker_Rel.try_teq true env
                  lc.FStar_Syntax_Syntax.res_typ t
                 in
              (uu____7208, false)
            else
              (let uu____7214 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env
                   lc.FStar_Syntax_Syntax.res_typ t
                  in
               (uu____7214, true))
             in
          match gopt with
          | (FStar_Pervasives_Native.None ,uu____7225) ->
              if env.FStar_TypeChecker_Env.failhard
              then
                let uu____7234 =
                  FStar_TypeChecker_Err.basic_type_error env
                    (FStar_Pervasives_Native.Some e) t
                    lc.FStar_Syntax_Syntax.res_typ
                   in
                FStar_Errors.raise_error uu____7234 e.FStar_Syntax_Syntax.pos
              else
                (FStar_TypeChecker_Rel.subtype_fail env e
                   lc.FStar_Syntax_Syntax.res_typ t;
                 (e,
                   ((let uu___132_7248 = lc  in
                     {
                       FStar_Syntax_Syntax.eff_name =
                         (uu___132_7248.FStar_Syntax_Syntax.eff_name);
                       FStar_Syntax_Syntax.res_typ = t;
                       FStar_Syntax_Syntax.cflags =
                         (uu___132_7248.FStar_Syntax_Syntax.cflags);
                       FStar_Syntax_Syntax.comp_thunk =
                         (uu___132_7248.FStar_Syntax_Syntax.comp_thunk)
                     })), FStar_TypeChecker_Rel.trivial_guard))
          | (FStar_Pervasives_Native.Some g,apply_guard1) ->
              let uu____7253 = FStar_TypeChecker_Rel.guard_form g  in
              (match uu____7253 with
               | FStar_TypeChecker_Common.Trivial  ->
                   let uu____7260 = FStar_Syntax_Util.set_result_typ_lc lc t
                      in
                   (e, uu____7260, g)
               | FStar_TypeChecker_Common.NonTrivial f ->
                   let g1 =
                     let uu___133_7263 = g  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___133_7263.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___133_7263.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___133_7263.FStar_TypeChecker_Env.implicits)
                     }  in
                   let strengthen uu____7269 =
                     let uu____7270 =
                       env.FStar_TypeChecker_Env.lax &&
                         (FStar_Options.ml_ish ())
                        in
                     if uu____7270
                     then FStar_Syntax_Syntax.lcomp_comp lc
                     else
                       (let f1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Normalize.Beta;
                            FStar_TypeChecker_Normalize.Eager_unfolding;
                            FStar_TypeChecker_Normalize.Simplify;
                            FStar_TypeChecker_Normalize.Primops] env f
                           in
                        let uu____7273 =
                          let uu____7274 = FStar_Syntax_Subst.compress f1  in
                          uu____7274.FStar_Syntax_Syntax.n  in
                        match uu____7273 with
                        | FStar_Syntax_Syntax.Tm_abs
                            (uu____7277,{
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.pos =
                                            uu____7279;
                                          FStar_Syntax_Syntax.vars =
                                            uu____7280;_},uu____7281)
                            when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.true_lid
                            ->
                            let lc1 =
                              let uu___134_7303 = lc  in
                              {
                                FStar_Syntax_Syntax.eff_name =
                                  (uu___134_7303.FStar_Syntax_Syntax.eff_name);
                                FStar_Syntax_Syntax.res_typ = t;
                                FStar_Syntax_Syntax.cflags =
                                  (uu___134_7303.FStar_Syntax_Syntax.cflags);
                                FStar_Syntax_Syntax.comp_thunk =
                                  (uu___134_7303.FStar_Syntax_Syntax.comp_thunk)
                              }  in
                            FStar_Syntax_Syntax.lcomp_comp lc1
                        | uu____7304 ->
                            let c = FStar_Syntax_Syntax.lcomp_comp lc  in
                            ((let uu____7307 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Extreme
                                 in
                              if uu____7307
                              then
                                let uu____7308 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env lc.FStar_Syntax_Syntax.res_typ
                                   in
                                let uu____7309 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env t
                                   in
                                let uu____7310 =
                                  FStar_TypeChecker_Normalize.comp_to_string
                                    env c
                                   in
                                let uu____7311 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env f1
                                   in
                                FStar_Util.print4
                                  "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                                  uu____7308 uu____7309 uu____7310 uu____7311
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
                                  let uu____7320 =
                                    let uu____7325 =
                                      let uu____7326 =
                                        FStar_Syntax_Syntax.as_arg xexp  in
                                      [uu____7326]  in
                                    FStar_Syntax_Syntax.mk_Tm_app f1
                                      uu____7325
                                     in
                                  uu____7320 FStar_Pervasives_Native.None
                                    f1.FStar_Syntax_Syntax.pos
                                else f1  in
                              let uu____7348 =
                                let uu____7353 =
                                  FStar_All.pipe_left
                                    (fun _0_16  ->
                                       FStar_Pervasives_Native.Some _0_16)
                                    (FStar_TypeChecker_Err.subtyping_failed
                                       env lc.FStar_Syntax_Syntax.res_typ t)
                                   in
                                let uu____7370 =
                                  FStar_TypeChecker_Env.set_range env
                                    e.FStar_Syntax_Syntax.pos
                                   in
                                let uu____7371 =
                                  FStar_Syntax_Util.lcomp_of_comp cret  in
                                let uu____7372 =
                                  FStar_All.pipe_left
                                    FStar_TypeChecker_Rel.guard_of_guard_formula
                                    (FStar_TypeChecker_Common.NonTrivial
                                       guard)
                                   in
                                strengthen_precondition uu____7353 uu____7370
                                  e uu____7371 uu____7372
                                 in
                              match uu____7348 with
                              | (eq_ret,_trivial_so_ok_to_discard) ->
                                  let x1 =
                                    let uu___135_7376 = x  in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___135_7376.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___135_7376.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort =
                                        (lc.FStar_Syntax_Syntax.res_typ)
                                    }  in
                                  let c1 =
                                    let uu____7378 =
                                      FStar_Syntax_Util.lcomp_of_comp c  in
                                    bind e.FStar_Syntax_Syntax.pos env
                                      (FStar_Pervasives_Native.Some e)
                                      uu____7378
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret)
                                     in
                                  let c2 = FStar_Syntax_Syntax.lcomp_comp c1
                                     in
                                  ((let uu____7383 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env)
                                        FStar_Options.Extreme
                                       in
                                    if uu____7383
                                    then
                                      let uu____7384 =
                                        FStar_TypeChecker_Normalize.comp_to_string
                                          env c2
                                         in
                                      FStar_Util.print1
                                        "Strengthened to %s\n" uu____7384
                                    else ());
                                   c2))))
                      in
                   let flags1 =
                     FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
                       (FStar_List.collect
                          (fun uu___106_7394  ->
                             match uu___106_7394 with
                             | FStar_Syntax_Syntax.RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.PARTIAL_RETURN  ->
                                 [FStar_Syntax_Syntax.PARTIAL_RETURN]
                             | FStar_Syntax_Syntax.CPS  ->
                                 [FStar_Syntax_Syntax.CPS]
                             | uu____7397 -> []))
                      in
                   let lc1 =
                     let uu____7399 =
                       FStar_TypeChecker_Env.norm_eff_name env
                         lc.FStar_Syntax_Syntax.eff_name
                        in
                     FStar_Syntax_Syntax.mk_lcomp uu____7399 t flags1
                       strengthen
                      in
                   let g2 =
                     let uu___136_7401 = g1  in
                     {
                       FStar_TypeChecker_Env.guard_f =
                         FStar_TypeChecker_Common.Trivial;
                       FStar_TypeChecker_Env.deferred =
                         (uu___136_7401.FStar_TypeChecker_Env.deferred);
                       FStar_TypeChecker_Env.univ_ineqs =
                         (uu___136_7401.FStar_TypeChecker_Env.univ_ineqs);
                       FStar_TypeChecker_Env.implicits =
                         (uu___136_7401.FStar_TypeChecker_Env.implicits)
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
        let uu____7436 =
          let uu____7439 =
            let uu____7444 =
              let uu____7445 =
                let uu____7452 = FStar_Syntax_Syntax.bv_to_name x  in
                FStar_Syntax_Syntax.as_arg uu____7452  in
              [uu____7445]  in
            FStar_Syntax_Syntax.mk_Tm_app ens uu____7444  in
          uu____7439 FStar_Pervasives_Native.None
            res_t.FStar_Syntax_Syntax.pos
           in
        FStar_Syntax_Util.refine x uu____7436  in
      let norm1 t =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env t
         in
      let uu____7473 = FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
      if uu____7473
      then
        (FStar_Pervasives_Native.None, (FStar_Syntax_Util.comp_result comp))
      else
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.GTotal uu____7489 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Total uu____7504 -> failwith "Impossible"
         | FStar_Syntax_Syntax.Comp ct ->
             let uu____7520 =
               (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_Pure_lid)
                 ||
                 (FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                    FStar_Parser_Const.effect_Ghost_lid)
                in
             if uu____7520
             then
               (match ct.FStar_Syntax_Syntax.effect_args with
                | (req,uu____7534)::(ens,uu____7536)::uu____7537 ->
                    let uu____7566 =
                      let uu____7569 = norm1 req  in
                      FStar_Pervasives_Native.Some uu____7569  in
                    let uu____7570 =
                      let uu____7571 =
                        mk_post_type ct.FStar_Syntax_Syntax.result_typ ens
                         in
                      FStar_All.pipe_left norm1 uu____7571  in
                    (uu____7566, uu____7570)
                | uu____7574 ->
                    let uu____7583 =
                      let uu____7588 =
                        let uu____7589 =
                          FStar_Syntax_Print.comp_to_string comp  in
                        FStar_Util.format1
                          "Effect constructor is not fully applied; got %s"
                          uu____7589
                         in
                      (FStar_Errors.Fatal_EffectConstructorNotFullyApplied,
                        uu____7588)
                       in
                    FStar_Errors.raise_error uu____7583
                      comp.FStar_Syntax_Syntax.pos)
             else
               (let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env comp
                   in
                match ct1.FStar_Syntax_Syntax.effect_args with
                | (wp,uu____7605)::uu____7606 ->
                    let uu____7625 =
                      let uu____7630 =
                        FStar_TypeChecker_Env.lookup_lid env
                          FStar_Parser_Const.as_requires
                         in
                      FStar_All.pipe_left FStar_Pervasives_Native.fst
                        uu____7630
                       in
                    (match uu____7625 with
                     | (us_r,uu____7662) ->
                         let uu____7663 =
                           let uu____7668 =
                             FStar_TypeChecker_Env.lookup_lid env
                               FStar_Parser_Const.as_ensures
                              in
                           FStar_All.pipe_left FStar_Pervasives_Native.fst
                             uu____7668
                            in
                         (match uu____7663 with
                          | (us_e,uu____7700) ->
                              let r =
                                (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let as_req =
                                let uu____7703 =
                                  let uu____7704 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_requires r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7704
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7703
                                  us_r
                                 in
                              let as_ens =
                                let uu____7706 =
                                  let uu____7707 =
                                    FStar_Ident.set_lid_range
                                      FStar_Parser_Const.as_ensures r
                                     in
                                  FStar_Syntax_Syntax.fvar uu____7707
                                    FStar_Syntax_Syntax.delta_equational
                                    FStar_Pervasives_Native.None
                                   in
                                FStar_Syntax_Syntax.mk_Tm_uinst uu____7706
                                  us_e
                                 in
                              let req =
                                let uu____7711 =
                                  let uu____7716 =
                                    let uu____7717 =
                                      let uu____7726 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7726]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7717
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_req
                                    uu____7716
                                   in
                                uu____7711 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let ens =
                                let uu____7758 =
                                  let uu____7763 =
                                    let uu____7764 =
                                      let uu____7773 =
                                        FStar_Syntax_Syntax.as_arg wp  in
                                      [uu____7773]  in
                                    ((ct1.FStar_Syntax_Syntax.result_typ),
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.imp_tag))
                                      :: uu____7764
                                     in
                                  FStar_Syntax_Syntax.mk_Tm_app as_ens
                                    uu____7763
                                   in
                                uu____7758 FStar_Pervasives_Native.None
                                  (ct1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
                                 in
                              let uu____7802 =
                                let uu____7805 = norm1 req  in
                                FStar_Pervasives_Native.Some uu____7805  in
                              let uu____7806 =
                                let uu____7807 =
                                  mk_post_type
                                    ct1.FStar_Syntax_Syntax.result_typ ens
                                   in
                                norm1 uu____7807  in
                              (uu____7802, uu____7806)))
                | uu____7810 -> failwith "Impossible"))
  
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
      (let uu____7840 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify")
          in
       if uu____7840
       then
         let uu____7841 = FStar_Syntax_Print.term_to_string tm  in
         let uu____7842 = FStar_Syntax_Print.term_to_string tm'  in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____7841 uu____7842
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
        (let uu____7886 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "SMTEncodingReify")
            in
         if uu____7886
         then
           let uu____7887 = FStar_Syntax_Print.term_to_string tm  in
           let uu____7888 = FStar_Syntax_Print.term_to_string tm'  in
           FStar_Util.print2 "Reified body %s \nto %s\n" uu____7887
             uu____7888
         else ());
        tm'
  
let (remove_reify : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____7895 =
      let uu____7896 =
        let uu____7897 = FStar_Syntax_Subst.compress t  in
        uu____7897.FStar_Syntax_Syntax.n  in
      match uu____7896 with
      | FStar_Syntax_Syntax.Tm_app uu____7900 -> false
      | uu____7915 -> true  in
    if uu____7895
    then t
    else
      (let uu____7917 = FStar_Syntax_Util.head_and_args t  in
       match uu____7917 with
       | (head1,args) ->
           let uu____7954 =
             let uu____7955 =
               let uu____7956 = FStar_Syntax_Subst.compress head1  in
               uu____7956.FStar_Syntax_Syntax.n  in
             match uu____7955 with
             | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
                 true
             | uu____7959 -> false  in
           if uu____7954
           then
             (match args with
              | x::[] -> FStar_Pervasives_Native.fst x
              | uu____7981 ->
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
             let uu____8026 = FStar_Syntax_Util.arrow_formals t1  in
             match uu____8026 with
             | (formals,uu____8040) ->
                 let n_implicits =
                   let uu____8058 =
                     FStar_All.pipe_right formals
                       (FStar_Util.prefix_until
                          (fun uu____8136  ->
                             match uu____8136 with
                             | (uu____8143,imp) ->
                                 (imp = FStar_Pervasives_Native.None) ||
                                   (imp =
                                      (FStar_Pervasives_Native.Some
                                         FStar_Syntax_Syntax.Equality))))
                      in
                   match uu____8058 with
                   | FStar_Pervasives_Native.None  ->
                       FStar_List.length formals
                   | FStar_Pervasives_Native.Some
                       (implicits,_first_explicit,_rest) ->
                       FStar_List.length implicits
                    in
                 n_implicits
              in
           let inst_n_binders t1 =
             let uu____8276 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____8276 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some expected_t ->
                 let n_expected = number_of_implicits expected_t  in
                 let n_available = number_of_implicits t1  in
                 if n_available < n_expected
                 then
                   let uu____8300 =
                     let uu____8305 =
                       let uu____8306 = FStar_Util.string_of_int n_expected
                          in
                       let uu____8313 = FStar_Syntax_Print.term_to_string e
                          in
                       let uu____8314 = FStar_Util.string_of_int n_available
                          in
                       FStar_Util.format3
                         "Expected a term with %s implicit arguments, but %s has only %s"
                         uu____8306 uu____8313 uu____8314
                        in
                     (FStar_Errors.Fatal_MissingImplicitArguments,
                       uu____8305)
                      in
                   let uu____8321 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____8300 uu____8321
                 else FStar_Pervasives_Native.Some (n_available - n_expected)
              in
           let decr_inst uu___107_8344 =
             match uu___107_8344 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some i ->
                 FStar_Pervasives_Native.Some (i - (Prims.parse_int "1"))
              in
           match torig.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               let uu____8374 = FStar_Syntax_Subst.open_comp bs c  in
               (match uu____8374 with
                | (bs1,c1) ->
                    let rec aux subst1 inst_n bs2 =
                      match (inst_n, bs2) with
                      | (FStar_Pervasives_Native.Some _0_17,uu____8489) when
                          _0_17 = (Prims.parse_int "0") ->
                          ([], bs2, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                      | (uu____8532,(x,FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Implicit dot))::rest)
                          ->
                          let t1 =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____8565 =
                            new_implicit_var
                              "Instantiation of implicit argument"
                              e.FStar_Syntax_Syntax.pos env t1
                             in
                          (match uu____8565 with
                           | (v1,uu____8605,g) ->
                               let subst2 = (FStar_Syntax_Syntax.NT (x, v1))
                                 :: subst1  in
                               let uu____8624 =
                                 aux subst2 (decr_inst inst_n) rest  in
                               (match uu____8624 with
                                | (args,bs3,subst3,g') ->
                                    let uu____8717 =
                                      FStar_TypeChecker_Rel.conj_guard g g'
                                       in
                                    (((v1,
                                        (FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit dot)))
                                      :: args), bs3, subst3, uu____8717)))
                      | (uu____8744,bs3) ->
                          ([], bs3, subst1,
                            FStar_TypeChecker_Rel.trivial_guard)
                       in
                    let uu____8790 =
                      let uu____8817 = inst_n_binders t  in
                      aux [] uu____8817 bs1  in
                    (match uu____8790 with
                     | (args,bs2,subst1,guard) ->
                         (match (args, bs2) with
                          | ([],uu____8888) -> (e, torig, guard)
                          | (uu____8919,[]) when
                              let uu____8950 =
                                FStar_Syntax_Util.is_total_comp c1  in
                              Prims.op_Negation uu____8950 ->
                              (e, torig, FStar_TypeChecker_Rel.trivial_guard)
                          | uu____8951 ->
                              let t1 =
                                match bs2 with
                                | [] -> FStar_Syntax_Util.comp_result c1
                                | uu____8979 ->
                                    FStar_Syntax_Util.arrow bs2 c1
                                 in
                              let t2 = FStar_Syntax_Subst.subst subst1 t1  in
                              let e1 =
                                FStar_Syntax_Syntax.mk_Tm_app e args
                                  FStar_Pervasives_Native.None
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              (e1, t2, guard))))
           | uu____8992 -> (e, t, FStar_TypeChecker_Rel.trivial_guard))
  
let (string_of_univs :
  FStar_Syntax_Syntax.universe_uvar FStar_Util.set -> Prims.string) =
  fun univs1  ->
    let uu____9002 =
      let uu____9005 = FStar_Util.set_elements univs1  in
      FStar_All.pipe_right uu____9005
        (FStar_List.map
           (fun u  ->
              let uu____9015 = FStar_Syntax_Unionfind.univ_uvar_id u  in
              FStar_All.pipe_right uu____9015 FStar_Util.string_of_int))
       in
    FStar_All.pipe_right uu____9002 (FStar_String.concat ", ")
  
let (gen_univs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set ->
      FStar_Syntax_Syntax.univ_name Prims.list)
  =
  fun env  ->
    fun x  ->
      let uu____9036 = FStar_Util.set_is_empty x  in
      if uu____9036
      then []
      else
        (let s =
           let uu____9051 =
             let uu____9054 = FStar_TypeChecker_Env.univ_vars env  in
             FStar_Util.set_difference x uu____9054  in
           FStar_All.pipe_right uu____9051 FStar_Util.set_elements  in
         (let uu____9070 =
            FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
              (FStar_Options.Other "Gen")
             in
          if uu____9070
          then
            let uu____9071 =
              let uu____9072 = FStar_TypeChecker_Env.univ_vars env  in
              string_of_univs uu____9072  in
            FStar_Util.print1 "univ_vars in env: %s\n" uu____9071
          else ());
         (let r =
            let uu____9079 = FStar_TypeChecker_Env.get_range env  in
            FStar_Pervasives_Native.Some uu____9079  in
          let u_names =
            FStar_All.pipe_right s
              (FStar_List.map
                 (fun u  ->
                    let u_name = FStar_Syntax_Syntax.new_univ_name r  in
                    (let uu____9118 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Gen")
                        in
                     if uu____9118
                     then
                       let uu____9119 =
                         let uu____9120 =
                           FStar_Syntax_Unionfind.univ_uvar_id u  in
                         FStar_All.pipe_left FStar_Util.string_of_int
                           uu____9120
                          in
                       let uu____9121 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_unif u)
                          in
                       let uu____9122 =
                         FStar_Syntax_Print.univ_to_string
                           (FStar_Syntax_Syntax.U_name u_name)
                          in
                       FStar_Util.print3 "Setting ?%s (%s) to %s\n"
                         uu____9119 uu____9121 uu____9122
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
        let uu____9148 = FStar_Util.set_difference tm_univnames ctx_univnames
           in
        FStar_All.pipe_right uu____9148 FStar_Util.set_elements  in
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
        | ([],uu____9186) -> generalized_univ_names
        | (uu____9193,[]) -> explicit_univ_names
        | uu____9200 ->
            let uu____9209 =
              let uu____9214 =
                let uu____9215 = FStar_Syntax_Print.term_to_string t  in
                Prims.strcat
                  "Generalized universe in a term containing explicit universe annotation : "
                  uu____9215
                 in
              (FStar_Errors.Fatal_UnexpectedGeneralizedUniverse, uu____9214)
               in
            FStar_Errors.raise_error uu____9209 t.FStar_Syntax_Syntax.pos
  
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
      (let uu____9233 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Gen")
          in
       if uu____9233
       then
         let uu____9234 = FStar_Syntax_Print.term_to_string t  in
         let uu____9235 = FStar_Syntax_Print.univ_names_to_string univnames1
            in
         FStar_Util.print2
           "generalizing universes in the term (post norm): %s with univnames: %s\n"
           uu____9234 uu____9235
       else ());
      (let univs1 = FStar_Syntax_Free.univs t  in
       (let uu____9241 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "Gen")
           in
        if uu____9241
        then
          let uu____9242 = string_of_univs univs1  in
          FStar_Util.print1 "univs to gen : %s\n" uu____9242
        else ());
       (let gen1 = gen_univs env univs1  in
        (let uu____9248 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Gen")
            in
         if uu____9248
         then
           let uu____9249 = FStar_Syntax_Print.term_to_string t  in
           let uu____9250 = FStar_Syntax_Print.univ_names_to_string gen1  in
           FStar_Util.print2 "After generalization, t: %s and univs: %s\n"
             uu____9249 uu____9250
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
        let uu____9328 =
          let uu____9329 =
            FStar_Util.for_all
              (fun uu____9342  ->
                 match uu____9342 with
                 | (uu____9351,uu____9352,c) ->
                     FStar_Syntax_Util.is_pure_or_ghost_comp c) lecs
             in
          FStar_All.pipe_left Prims.op_Negation uu____9329  in
        if uu____9328
        then FStar_Pervasives_Native.None
        else
          (let norm1 c =
             (let uu____9400 =
                FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
              if uu____9400
              then
                let uu____9401 = FStar_Syntax_Print.comp_to_string c  in
                FStar_Util.print1 "Normalizing before generalizing:\n\t %s\n"
                  uu____9401
              else ());
             (let c1 =
                FStar_TypeChecker_Normalize.normalize_comp
                  [FStar_TypeChecker_Normalize.Beta;
                  FStar_TypeChecker_Normalize.Exclude
                    FStar_TypeChecker_Normalize.Zeta;
                  FStar_TypeChecker_Normalize.NoFullNorm;
                  FStar_TypeChecker_Normalize.DoNotUnfoldPureLets] env c
                 in
              (let uu____9405 =
                 FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
               if uu____9405
               then
                 let uu____9406 = FStar_Syntax_Print.comp_to_string c1  in
                 FStar_Util.print1 "Normalized to:\n\t %s\n" uu____9406
               else ());
              c1)
              in
           let env_uvars = FStar_TypeChecker_Env.uvars_in_env env  in
           let gen_uvars uvs =
             let uu____9421 = FStar_Util.set_difference uvs env_uvars  in
             FStar_All.pipe_right uu____9421 FStar_Util.set_elements  in
           let univs_and_uvars_of_lec uu____9457 =
             match uu____9457 with
             | (lbname,e,c) ->
                 let t =
                   FStar_All.pipe_right (FStar_Syntax_Util.comp_result c)
                     FStar_Syntax_Subst.compress
                    in
                 let c1 = norm1 c  in
                 let t1 = FStar_Syntax_Util.comp_result c1  in
                 let univs1 = FStar_Syntax_Free.univs t1  in
                 let uvt = FStar_Syntax_Free.uvars t1  in
                 ((let uu____9501 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "Gen")
                      in
                   if uu____9501
                   then
                     let uu____9502 =
                       let uu____9503 =
                         let uu____9506 = FStar_Util.set_elements univs1  in
                         FStar_All.pipe_right uu____9506
                           (FStar_List.map
                              (fun u  ->
                                 FStar_Syntax_Print.univ_to_string
                                   (FStar_Syntax_Syntax.U_unif u)))
                          in
                       FStar_All.pipe_right uu____9503
                         (FStar_String.concat ", ")
                        in
                     let uu____9549 =
                       let uu____9550 =
                         let uu____9553 = FStar_Util.set_elements uvt  in
                         FStar_All.pipe_right uu____9553
                           (FStar_List.map
                              (fun u  ->
                                 let uu____9564 =
                                   FStar_Syntax_Print.uvar_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_head
                                    in
                                 let uu____9565 =
                                   FStar_Syntax_Print.term_to_string
                                     u.FStar_Syntax_Syntax.ctx_uvar_typ
                                    in
                                 FStar_Util.format2 "(%s : %s)" uu____9564
                                   uu____9565))
                          in
                       FStar_All.pipe_right uu____9550
                         (FStar_String.concat ", ")
                        in
                     FStar_Util.print2
                       "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n" uu____9502
                       uu____9549
                   else ());
                  (let univs2 =
                     let uu____9572 = FStar_Util.set_elements uvt  in
                     FStar_List.fold_left
                       (fun univs2  ->
                          fun uv  ->
                            let uu____9584 =
                              FStar_Syntax_Free.univs
                                uv.FStar_Syntax_Syntax.ctx_uvar_typ
                               in
                            FStar_Util.set_union univs2 uu____9584) univs1
                       uu____9572
                      in
                   let uvs = gen_uvars uvt  in
                   (let uu____9591 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        (FStar_Options.Other "Gen")
                       in
                    if uu____9591
                    then
                      let uu____9592 =
                        let uu____9593 =
                          let uu____9596 = FStar_Util.set_elements univs2  in
                          FStar_All.pipe_right uu____9596
                            (FStar_List.map
                               (fun u  ->
                                  FStar_Syntax_Print.univ_to_string
                                    (FStar_Syntax_Syntax.U_unif u)))
                           in
                        FStar_All.pipe_right uu____9593
                          (FStar_String.concat ", ")
                         in
                      let uu____9639 =
                        let uu____9640 =
                          FStar_All.pipe_right uvs
                            (FStar_List.map
                               (fun u  ->
                                  let uu____9651 =
                                    FStar_Syntax_Print.uvar_to_string
                                      u.FStar_Syntax_Syntax.ctx_uvar_head
                                     in
                                  let uu____9652 =
                                    FStar_TypeChecker_Normalize.term_to_string
                                      env u.FStar_Syntax_Syntax.ctx_uvar_typ
                                     in
                                  FStar_Util.format2 "(%s : %s)" uu____9651
                                    uu____9652))
                           in
                        FStar_All.pipe_right uu____9640
                          (FStar_String.concat ", ")
                         in
                      FStar_Util.print2
                        "^^^^\n\tFree univs = %s\n\tgen_uvars =%s" uu____9592
                        uu____9639
                    else ());
                   (univs2, uvs, (lbname, e, c1))))
              in
           let uu____9666 =
             let uu____9683 = FStar_List.hd lecs  in
             univs_and_uvars_of_lec uu____9683  in
           match uu____9666 with
           | (univs1,uvs,lec_hd) ->
               let force_univs_eq lec2 u1 u2 =
                 let uu____9775 =
                   (FStar_Util.set_is_subset_of u1 u2) &&
                     (FStar_Util.set_is_subset_of u2 u1)
                    in
                 if uu____9775
                 then ()
                 else
                   (let uu____9777 = lec_hd  in
                    match uu____9777 with
                    | (lb1,uu____9785,uu____9786) ->
                        let uu____9787 = lec2  in
                        (match uu____9787 with
                         | (lb2,uu____9795,uu____9796) ->
                             let msg =
                               let uu____9798 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9799 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible set of universes for %s and %s"
                                 uu____9798 uu____9799
                                in
                             let uu____9800 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleSetOfUniverse,
                                 msg) uu____9800))
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
                 let uu____9864 =
                   (uvars_subseteq u1 u2) && (uvars_subseteq u2 u1)  in
                 if uu____9864
                 then ()
                 else
                   (let uu____9866 = lec_hd  in
                    match uu____9866 with
                    | (lb1,uu____9874,uu____9875) ->
                        let uu____9876 = lec2  in
                        (match uu____9876 with
                         | (lb2,uu____9884,uu____9885) ->
                             let msg =
                               let uu____9887 =
                                 FStar_Syntax_Print.lbname_to_string lb1  in
                               let uu____9888 =
                                 FStar_Syntax_Print.lbname_to_string lb2  in
                               FStar_Util.format2
                                 "Generalizing the types of these mutually recursive definitions requires an incompatible number of types for %s and %s"
                                 uu____9887 uu____9888
                                in
                             let uu____9889 =
                               FStar_TypeChecker_Env.get_range env  in
                             FStar_Errors.raise_error
                               (FStar_Errors.Fatal_IncompatibleNumberOfTypes,
                                 msg) uu____9889))
                  in
               let lecs1 =
                 let uu____9899 = FStar_List.tl lecs  in
                 FStar_List.fold_right
                   (fun this_lec  ->
                      fun lecs1  ->
                        let uu____9958 = univs_and_uvars_of_lec this_lec  in
                        match uu____9958 with
                        | (this_univs,this_uvs,this_lec1) ->
                            (force_univs_eq this_lec1 univs1 this_univs;
                             force_uvars_eq this_lec1 uvs this_uvs;
                             this_lec1
                             ::
                             lecs1)) uu____9899 []
                  in
               let lecs2 = lec_hd :: lecs1  in
               let gen_types uvs1 =
                 let fail1 k =
                   let uu____10059 = lec_hd  in
                   match uu____10059 with
                   | (lbname,e,c) ->
                       let uu____10069 =
                         let uu____10074 =
                           let uu____10075 =
                             FStar_Syntax_Print.term_to_string k  in
                           let uu____10076 =
                             FStar_Syntax_Print.lbname_to_string lbname  in
                           let uu____10077 =
                             FStar_Syntax_Print.term_to_string
                               (FStar_Syntax_Util.comp_result c)
                              in
                           FStar_Util.format3
                             "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                             uu____10075 uu____10076 uu____10077
                            in
                         (FStar_Errors.Fatal_FailToResolveImplicitArgument,
                           uu____10074)
                          in
                       let uu____10078 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____10069 uu____10078
                    in
                 FStar_All.pipe_right uvs1
                   (FStar_List.map
                      (fun u  ->
                         let uu____10099 =
                           FStar_Syntax_Unionfind.find
                             u.FStar_Syntax_Syntax.ctx_uvar_head
                            in
                         match uu____10099 with
                         | FStar_Pervasives_Native.Some uu____10108 ->
                             failwith
                               "Unexpected instantiation of mutually recursive uvar"
                         | uu____10115 ->
                             let k =
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Normalize.Beta;
                                 FStar_TypeChecker_Normalize.Exclude
                                   FStar_TypeChecker_Normalize.Zeta] env
                                 u.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             let uu____10119 =
                               FStar_Syntax_Util.arrow_formals k  in
                             (match uu____10119 with
                              | (bs,kres) ->
                                  ((let uu____10157 =
                                      let uu____10158 =
                                        let uu____10161 =
                                          FStar_TypeChecker_Normalize.unfold_whnf
                                            env kres
                                           in
                                        FStar_Syntax_Util.unrefine
                                          uu____10161
                                         in
                                      uu____10158.FStar_Syntax_Syntax.n  in
                                    match uu____10157 with
                                    | FStar_Syntax_Syntax.Tm_type uu____10162
                                        ->
                                        let free =
                                          FStar_Syntax_Free.names kres  in
                                        let uu____10166 =
                                          let uu____10167 =
                                            FStar_Util.set_is_empty free  in
                                          Prims.op_Negation uu____10167  in
                                        if uu____10166
                                        then fail1 kres
                                        else ()
                                    | uu____10169 -> fail1 kres);
                                   (let a =
                                      let uu____10171 =
                                        let uu____10174 =
                                          FStar_TypeChecker_Env.get_range env
                                           in
                                        FStar_All.pipe_left
                                          (fun _0_18  ->
                                             FStar_Pervasives_Native.Some
                                               _0_18) uu____10174
                                         in
                                      FStar_Syntax_Syntax.new_bv uu____10171
                                        kres
                                       in
                                    let t =
                                      match bs with
                                      | [] ->
                                          FStar_Syntax_Syntax.bv_to_name a
                                      | uu____10182 ->
                                          let uu____10189 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Util.abs bs
                                            uu____10189
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
                      (fun uu____10300  ->
                         match uu____10300 with
                         | (lbname,e,c) ->
                             let uu____10354 =
                               match (gen_tvars, gen_univs1) with
                               | ([],[]) -> (e, c, [])
                               | uu____10429 ->
                                   let uu____10444 = (e, c)  in
                                   (match uu____10444 with
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
                                                (fun uu____10495  ->
                                                   match uu____10495 with
                                                   | (x,uu____10503) ->
                                                       let uu____10508 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x
                                                          in
                                                       FStar_Syntax_Syntax.iarg
                                                         uu____10508)
                                                gen_tvars
                                               in
                                            let instantiate_lbname_with_app
                                              tm fv =
                                              let uu____10526 =
                                                let uu____10527 =
                                                  FStar_Util.right lbname  in
                                                FStar_Syntax_Syntax.fv_eq fv
                                                  uu____10527
                                                 in
                                              if uu____10526
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
                                          let uu____10533 =
                                            let uu____10534 =
                                              FStar_Syntax_Subst.compress
                                                (FStar_Syntax_Util.comp_result
                                                   c1)
                                               in
                                            uu____10534.FStar_Syntax_Syntax.n
                                             in
                                          match uu____10533 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,cod) ->
                                              let uu____10555 =
                                                FStar_Syntax_Subst.open_comp
                                                  bs cod
                                                 in
                                              (match uu____10555 with
                                               | (bs1,cod1) ->
                                                   FStar_Syntax_Util.arrow
                                                     (FStar_List.append
                                                        gen_tvars bs1) cod1)
                                          | uu____10568 ->
                                              FStar_Syntax_Util.arrow
                                                gen_tvars c1
                                           in
                                        let e' =
                                          FStar_Syntax_Util.abs gen_tvars e2
                                            (FStar_Pervasives_Native.Some
                                               (FStar_Syntax_Util.residual_comp_of_comp
                                                  c1))
                                           in
                                        let uu____10572 =
                                          FStar_Syntax_Syntax.mk_Total t  in
                                        (e', uu____10572, gen_tvars))
                                in
                             (match uu____10354 with
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
        (let uu____10726 = FStar_TypeChecker_Env.debug env FStar_Options.Low
            in
         if uu____10726
         then
           let uu____10727 =
             let uu____10728 =
               FStar_List.map
                 (fun uu____10741  ->
                    match uu____10741 with
                    | (lb,uu____10749,uu____10750) ->
                        FStar_Syntax_Print.lbname_to_string lb) lecs
                in
             FStar_All.pipe_right uu____10728 (FStar_String.concat ", ")  in
           FStar_Util.print1 "Generalizing: %s\n" uu____10727
         else ());
        (let univnames_lecs =
           FStar_List.map
             (fun uu____10771  ->
                match uu____10771 with
                | (l,t,c) -> gather_free_univnames env t) lecs
            in
         let generalized_lecs =
           let uu____10800 = gen env is_rec lecs  in
           match uu____10800 with
           | FStar_Pervasives_Native.None  ->
               FStar_All.pipe_right lecs
                 (FStar_List.map
                    (fun uu____10899  ->
                       match uu____10899 with | (l,t,c) -> (l, [], t, c, [])))
           | FStar_Pervasives_Native.Some luecs ->
               ((let uu____10961 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
                 if uu____10961
                 then
                   FStar_All.pipe_right luecs
                     (FStar_List.iter
                        (fun uu____11007  ->
                           match uu____11007 with
                           | (l,us,e,c,gvs) ->
                               let uu____11041 =
                                 FStar_Range.string_of_range
                                   e.FStar_Syntax_Syntax.pos
                                  in
                               let uu____11042 =
                                 FStar_Syntax_Print.lbname_to_string l  in
                               let uu____11043 =
                                 FStar_Syntax_Print.term_to_string
                                   (FStar_Syntax_Util.comp_result c)
                                  in
                               let uu____11044 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____11045 =
                                 FStar_Syntax_Print.binders_to_string ", "
                                   gvs
                                  in
                               FStar_Util.print5
                                 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                 uu____11041 uu____11042 uu____11043
                                 uu____11044 uu____11045))
                 else ());
                luecs)
            in
         FStar_List.map2
           (fun univnames1  ->
              fun uu____11086  ->
                match uu____11086 with
                | (l,generalized_univs,t,c,gvs) ->
                    let uu____11130 =
                      check_universe_generalization univnames1
                        generalized_univs t
                       in
                    (l, uu____11130, t, c, gvs)) univnames_lecs
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
              (let uu____11187 =
                 FStar_TypeChecker_Rel.get_subtyping_predicate env2 t11 t21
                  in
               match uu____11187 with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some f ->
                   let uu____11193 = FStar_TypeChecker_Rel.apply_guard f e
                      in
                   FStar_All.pipe_left
                     (fun _0_19  -> FStar_Pervasives_Native.Some _0_19)
                     uu____11193)
             in
          let is_var e1 =
            let uu____11202 =
              let uu____11203 = FStar_Syntax_Subst.compress e1  in
              uu____11203.FStar_Syntax_Syntax.n  in
            match uu____11202 with
            | FStar_Syntax_Syntax.Tm_name uu____11206 -> true
            | uu____11207 -> false  in
          let decorate e1 t =
            let e2 = FStar_Syntax_Subst.compress e1  in
            match e2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_name x ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_name
                     (let uu___137_11227 = x  in
                      {
                        FStar_Syntax_Syntax.ppname =
                          (uu___137_11227.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (uu___137_11227.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = t2
                      })) FStar_Pervasives_Native.None
                  e2.FStar_Syntax_Syntax.pos
            | uu____11228 -> e2  in
          let env2 =
            let uu___138_11230 = env1  in
            let uu____11231 =
              env1.FStar_TypeChecker_Env.use_eq ||
                (env1.FStar_TypeChecker_Env.is_pattern && (is_var e))
               in
            {
              FStar_TypeChecker_Env.solver =
                (uu___138_11230.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___138_11230.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___138_11230.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___138_11230.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___138_11230.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___138_11230.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___138_11230.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___138_11230.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___138_11230.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___138_11230.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___138_11230.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___138_11230.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___138_11230.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___138_11230.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___138_11230.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___138_11230.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq = uu____11231;
              FStar_TypeChecker_Env.is_iface =
                (uu___138_11230.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___138_11230.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___138_11230.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___138_11230.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.failhard =
                (uu___138_11230.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___138_11230.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___138_11230.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___138_11230.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___138_11230.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___138_11230.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___138_11230.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___138_11230.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___138_11230.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___138_11230.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.proof_ns =
                (uu___138_11230.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___138_11230.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___138_11230.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___138_11230.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___138_11230.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___138_11230.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___138_11230.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.dep_graph =
                (uu___138_11230.FStar_TypeChecker_Env.dep_graph)
            }  in
          let uu____11232 = check1 env2 t1 t2  in
          match uu____11232 with
          | FStar_Pervasives_Native.None  ->
              let uu____11239 =
                FStar_TypeChecker_Err.expected_expression_of_type env2 t2 e
                  t1
                 in
              let uu____11244 = FStar_TypeChecker_Env.get_range env2  in
              FStar_Errors.raise_error uu____11239 uu____11244
          | FStar_Pervasives_Native.Some g ->
              ((let uu____11251 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "Rel")
                   in
                if uu____11251
                then
                  let uu____11252 =
                    FStar_TypeChecker_Rel.guard_to_string env2 g  in
                  FStar_All.pipe_left
                    (FStar_Util.print1 "Applied guard is %s\n") uu____11252
                else ());
               (let uu____11254 = decorate e t2  in (uu____11254, g)))
  
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
        let uu____11286 = FStar_Syntax_Util.is_total_lcomp lc  in
        if uu____11286
        then
          let uu____11291 = discharge g1  in
          let uu____11292 = FStar_Syntax_Syntax.lcomp_comp lc  in
          (uu____11291, uu____11292)
        else
          (let c = FStar_Syntax_Syntax.lcomp_comp lc  in
           let steps =
             [FStar_TypeChecker_Normalize.Beta;
             FStar_TypeChecker_Normalize.NoFullNorm;
             FStar_TypeChecker_Normalize.DoNotUnfoldPureLets]  in
           let c1 =
             let uu____11299 =
               let uu____11300 =
                 let uu____11301 =
                   FStar_TypeChecker_Env.unfold_effect_abbrev env c  in
                 FStar_All.pipe_right uu____11301 FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____11300
                 (FStar_TypeChecker_Normalize.normalize_comp steps env)
                in
             FStar_All.pipe_right uu____11299
               (FStar_TypeChecker_Env.comp_to_comp_typ env)
              in
           let md =
             FStar_TypeChecker_Env.get_effect_decl env
               c1.FStar_Syntax_Syntax.effect_name
              in
           let uu____11303 = destruct_comp c1  in
           match uu____11303 with
           | (u_t,t,wp) ->
               let vc =
                 let uu____11320 = FStar_TypeChecker_Env.get_range env  in
                 let uu____11321 =
                   let uu____11326 =
                     FStar_TypeChecker_Env.inst_effect_fun_with [u_t] env md
                       md.FStar_Syntax_Syntax.trivial
                      in
                   let uu____11327 =
                     let uu____11328 = FStar_Syntax_Syntax.as_arg t  in
                     let uu____11335 =
                       let uu____11344 = FStar_Syntax_Syntax.as_arg wp  in
                       [uu____11344]  in
                     uu____11328 :: uu____11335  in
                   FStar_Syntax_Syntax.mk_Tm_app uu____11326 uu____11327  in
                 uu____11321 FStar_Pervasives_Native.None uu____11320  in
               ((let uu____11372 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Simplification")
                    in
                 if uu____11372
                 then
                   let uu____11373 = FStar_Syntax_Print.term_to_string vc  in
                   FStar_Util.print1 "top-level VC: %s\n" uu____11373
                 else ());
                (let g2 =
                   let uu____11376 =
                     FStar_All.pipe_left
                       FStar_TypeChecker_Rel.guard_of_guard_formula
                       (FStar_TypeChecker_Common.NonTrivial vc)
                      in
                   FStar_TypeChecker_Rel.conj_guard g1 uu____11376  in
                 let uu____11377 = discharge g2  in
                 let uu____11378 = FStar_Syntax_Syntax.mk_Comp c1  in
                 (uu____11377, uu____11378))))
  
let (short_circuit :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_TypeChecker_Common.guard_formula)
  =
  fun head1  ->
    fun seen_args  ->
      let short_bin_op f uu___108_11410 =
        match uu___108_11410 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (fst1,uu____11418)::[] -> f fst1
        | uu____11435 -> failwith "Unexpexted args to binary operator"  in
      let op_and_e e =
        let uu____11446 = FStar_Syntax_Util.b2t e  in
        FStar_All.pipe_right uu____11446
          (fun _0_20  -> FStar_TypeChecker_Common.NonTrivial _0_20)
         in
      let op_or_e e =
        let uu____11457 =
          let uu____11458 = FStar_Syntax_Util.b2t e  in
          FStar_Syntax_Util.mk_neg uu____11458  in
        FStar_All.pipe_right uu____11457
          (fun _0_21  -> FStar_TypeChecker_Common.NonTrivial _0_21)
         in
      let op_and_t t =
        FStar_All.pipe_right t
          (fun _0_22  -> FStar_TypeChecker_Common.NonTrivial _0_22)
         in
      let op_or_t t =
        let uu____11477 = FStar_All.pipe_right t FStar_Syntax_Util.mk_neg  in
        FStar_All.pipe_right uu____11477
          (fun _0_23  -> FStar_TypeChecker_Common.NonTrivial _0_23)
         in
      let op_imp_t t =
        FStar_All.pipe_right t
          (fun _0_24  -> FStar_TypeChecker_Common.NonTrivial _0_24)
         in
      let short_op_ite uu___109_11491 =
        match uu___109_11491 with
        | [] -> FStar_TypeChecker_Common.Trivial
        | (guard,uu____11499)::[] ->
            FStar_TypeChecker_Common.NonTrivial guard
        | _then::(guard,uu____11518)::[] ->
            let uu____11547 = FStar_Syntax_Util.mk_neg guard  in
            FStar_All.pipe_right uu____11547
              (fun _0_25  -> FStar_TypeChecker_Common.NonTrivial _0_25)
        | uu____11548 -> failwith "Unexpected args to ITE"  in
      let table =
        let uu____11559 =
          let uu____11567 = short_bin_op op_and_e  in
          (FStar_Parser_Const.op_And, uu____11567)  in
        let uu____11575 =
          let uu____11585 =
            let uu____11593 = short_bin_op op_or_e  in
            (FStar_Parser_Const.op_Or, uu____11593)  in
          let uu____11601 =
            let uu____11611 =
              let uu____11619 = short_bin_op op_and_t  in
              (FStar_Parser_Const.and_lid, uu____11619)  in
            let uu____11627 =
              let uu____11637 =
                let uu____11645 = short_bin_op op_or_t  in
                (FStar_Parser_Const.or_lid, uu____11645)  in
              let uu____11653 =
                let uu____11663 =
                  let uu____11671 = short_bin_op op_imp_t  in
                  (FStar_Parser_Const.imp_lid, uu____11671)  in
                [uu____11663; (FStar_Parser_Const.ite_lid, short_op_ite)]  in
              uu____11637 :: uu____11653  in
            uu____11611 :: uu____11627  in
          uu____11585 :: uu____11601  in
        uu____11559 :: uu____11575  in
      match head1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____11733 =
            FStar_Util.find_map table
              (fun uu____11748  ->
                 match uu____11748 with
                 | (x,mk1) ->
                     let uu____11765 = FStar_Ident.lid_equals x lid  in
                     if uu____11765
                     then
                       let uu____11768 = mk1 seen_args  in
                       FStar_Pervasives_Native.Some uu____11768
                     else FStar_Pervasives_Native.None)
             in
          (match uu____11733 with
           | FStar_Pervasives_Native.None  ->
               FStar_TypeChecker_Common.Trivial
           | FStar_Pervasives_Native.Some g -> g)
      | uu____11771 -> FStar_TypeChecker_Common.Trivial
  
let (short_circuit_head : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun l  ->
    let uu____11777 =
      let uu____11778 = FStar_Syntax_Util.un_uinst l  in
      uu____11778.FStar_Syntax_Syntax.n  in
    match uu____11777 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv)
          [FStar_Parser_Const.op_And;
          FStar_Parser_Const.op_Or;
          FStar_Parser_Const.and_lid;
          FStar_Parser_Const.or_lid;
          FStar_Parser_Const.imp_lid;
          FStar_Parser_Const.ite_lid]
    | uu____11782 -> false
  
let (maybe_add_implicit_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun env  ->
    fun bs  ->
      let pos bs1 =
        match bs1 with
        | (hd1,uu____11812)::uu____11813 ->
            FStar_Syntax_Syntax.range_of_bv hd1
        | uu____11824 -> FStar_TypeChecker_Env.get_range env  in
      match bs with
      | (uu____11831,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____11832))::uu____11833 -> bs
      | uu____11844 ->
          let uu____11845 = FStar_TypeChecker_Env.expected_typ env  in
          (match uu____11845 with
           | FStar_Pervasives_Native.None  -> bs
           | FStar_Pervasives_Native.Some t ->
               let uu____11849 =
                 let uu____11850 = FStar_Syntax_Subst.compress t  in
                 uu____11850.FStar_Syntax_Syntax.n  in
               (match uu____11849 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',uu____11854) ->
                    let uu____11871 =
                      FStar_Util.prefix_until
                        (fun uu___110_11911  ->
                           match uu___110_11911 with
                           | (uu____11918,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____11919)) ->
                               false
                           | uu____11922 -> true) bs'
                       in
                    (match uu____11871 with
                     | FStar_Pervasives_Native.None  -> bs
                     | FStar_Pervasives_Native.Some
                         ([],uu____11957,uu____11958) -> bs
                     | FStar_Pervasives_Native.Some
                         (imps,uu____12030,uu____12031) ->
                         let uu____12104 =
                           FStar_All.pipe_right imps
                             (FStar_Util.for_all
                                (fun uu____12122  ->
                                   match uu____12122 with
                                   | (x,uu____12130) ->
                                       FStar_Util.starts_with
                                         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                                         "'"))
                            in
                         if uu____12104
                         then
                           let r = pos bs  in
                           let imps1 =
                             FStar_All.pipe_right imps
                               (FStar_List.map
                                  (fun uu____12173  ->
                                     match uu____12173 with
                                     | (x,i) ->
                                         let uu____12192 =
                                           FStar_Syntax_Syntax.set_range_of_bv
                                             x r
                                            in
                                         (uu____12192, i)))
                              in
                           FStar_List.append imps1 bs
                         else bs)
                | uu____12200 -> bs))
  
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
            let uu____12228 =
              ((FStar_Ident.lid_equals m1 m2) ||
                 ((FStar_Syntax_Util.is_pure_effect c1) &&
                    (FStar_Syntax_Util.is_ghost_effect c2)))
                ||
                ((FStar_Syntax_Util.is_pure_effect c2) &&
                   (FStar_Syntax_Util.is_ghost_effect c1))
               in
            if uu____12228
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
          let uu____12255 =
            ((is_pure_or_ghost_effect env m) ||
               (FStar_Ident.lid_equals m FStar_Parser_Const.effect_Tot_lid))
              ||
              (FStar_Ident.lid_equals m FStar_Parser_Const.effect_GTot_lid)
             in
          if uu____12255
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
        (let uu____12290 =
           FStar_TypeChecker_Env.debug env (FStar_Options.Other "ED")  in
         if uu____12290
         then
           ((let uu____12292 = FStar_Ident.text_of_lid lident  in
             d uu____12292);
            (let uu____12293 = FStar_Ident.text_of_lid lident  in
             let uu____12294 = FStar_Syntax_Print.term_to_string def  in
             FStar_Util.print2 "Registering top-level definition: %s\n%s\n"
               uu____12293 uu____12294))
         else ());
        (let fv =
           let uu____12297 = FStar_Syntax_Util.incr_delta_qualifier def  in
           FStar_Syntax_Syntax.lid_as_fv lident uu____12297
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
         let uu____12307 =
           FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar fv)
             FStar_Pervasives_Native.None FStar_Range.dummyRange
            in
         ((let uu___139_12309 = sig_ctx  in
           {
             FStar_Syntax_Syntax.sigel =
               (uu___139_12309.FStar_Syntax_Syntax.sigel);
             FStar_Syntax_Syntax.sigrng =
               (uu___139_12309.FStar_Syntax_Syntax.sigrng);
             FStar_Syntax_Syntax.sigquals =
               [FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen];
             FStar_Syntax_Syntax.sigmeta =
               (uu___139_12309.FStar_Syntax_Syntax.sigmeta);
             FStar_Syntax_Syntax.sigattrs =
               (uu___139_12309.FStar_Syntax_Syntax.sigattrs)
           }), uu____12307))
  
let (check_sigelt_quals :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> unit) =
  fun env  ->
    fun se  ->
      let visibility uu___111_12325 =
        match uu___111_12325 with
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12326 -> false  in
      let reducibility uu___112_12332 =
        match uu___112_12332 with
        | FStar_Syntax_Syntax.Abstract  -> true
        | FStar_Syntax_Syntax.Irreducible  -> true
        | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen  -> true
        | FStar_Syntax_Syntax.Visible_default  -> true
        | FStar_Syntax_Syntax.Inline_for_extraction  -> true
        | uu____12333 -> false  in
      let assumption uu___113_12339 =
        match uu___113_12339 with
        | FStar_Syntax_Syntax.Assumption  -> true
        | FStar_Syntax_Syntax.New  -> true
        | uu____12340 -> false  in
      let reification uu___114_12346 =
        match uu___114_12346 with
        | FStar_Syntax_Syntax.Reifiable  -> true
        | FStar_Syntax_Syntax.Reflectable uu____12347 -> true
        | uu____12348 -> false  in
      let inferred uu___115_12354 =
        match uu___115_12354 with
        | FStar_Syntax_Syntax.Discriminator uu____12355 -> true
        | FStar_Syntax_Syntax.Projector uu____12356 -> true
        | FStar_Syntax_Syntax.RecordType uu____12361 -> true
        | FStar_Syntax_Syntax.RecordConstructor uu____12370 -> true
        | FStar_Syntax_Syntax.ExceptionConstructor  -> true
        | FStar_Syntax_Syntax.HasMaskedEffect  -> true
        | FStar_Syntax_Syntax.Effect  -> true
        | uu____12379 -> false  in
      let has_eq uu___116_12385 =
        match uu___116_12385 with
        | FStar_Syntax_Syntax.Noeq  -> true
        | FStar_Syntax_Syntax.Unopteq  -> true
        | uu____12386 -> false  in
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
        | FStar_Syntax_Syntax.Reflectable uu____12450 ->
            FStar_All.pipe_right quals
              (FStar_List.for_all
                 (fun x  ->
                    ((((reification x) || (inferred x)) || (visibility x)) ||
                       (x = FStar_Syntax_Syntax.TotalEffect))
                      || (x = FStar_Syntax_Syntax.Visible_default)))
        | FStar_Syntax_Syntax.Private  -> true
        | uu____12455 -> true  in
      let quals = FStar_Syntax_Util.quals_of_sigelt se  in
      let uu____12459 =
        let uu____12460 =
          FStar_All.pipe_right quals
            (FStar_Util.for_some
               (fun uu___117_12464  ->
                  match uu___117_12464 with
                  | FStar_Syntax_Syntax.OnlyName  -> true
                  | uu____12465 -> false))
           in
        FStar_All.pipe_right uu____12460 Prims.op_Negation  in
      if uu____12459
      then
        let r = FStar_Syntax_Util.range_of_sigelt se  in
        let no_dup_quals =
          FStar_Util.remove_dups (fun x  -> fun y  -> x = y) quals  in
        let err' msg =
          let uu____12480 =
            let uu____12485 =
              let uu____12486 = FStar_Syntax_Print.quals_to_string quals  in
              FStar_Util.format2
                "The qualifier list \"[%s]\" is not permissible for this element%s"
                uu____12486 msg
               in
            (FStar_Errors.Fatal_QulifierListNotPermitted, uu____12485)  in
          FStar_Errors.raise_error uu____12480 r  in
        let err msg = err' (Prims.strcat ": " msg)  in
        let err'1 uu____12498 = err' ""  in
        (if (FStar_List.length quals) <> (FStar_List.length no_dup_quals)
         then err "duplicate qualifiers"
         else ();
         (let uu____12502 =
            let uu____12503 =
              FStar_All.pipe_right quals
                (FStar_List.for_all (quals_combo_ok quals))
               in
            Prims.op_Negation uu____12503  in
          if uu____12502 then err "ill-formed combination" else ());
         (match se.FStar_Syntax_Syntax.sigel with
          | FStar_Syntax_Syntax.Sig_let ((is_rec,uu____12508),uu____12509) ->
              ((let uu____12519 =
                  is_rec &&
                    (FStar_All.pipe_right quals
                       (FStar_List.contains
                          FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen))
                   in
                if uu____12519
                then err "recursive definitions cannot be marked inline"
                else ());
               (let uu____12523 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun x  -> (assumption x) || (has_eq x)))
                   in
                if uu____12523
                then
                  err
                    "definitions cannot be assumed or marked with equality qualifiers"
                else ()))
          | FStar_Syntax_Syntax.Sig_bundle uu____12529 ->
              let uu____12538 =
                let uu____12539 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.Abstract) ||
                              (inferred x))
                             || (visibility x))
                            || (has_eq x)))
                   in
                Prims.op_Negation uu____12539  in
              if uu____12538 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_declare_typ uu____12545 ->
              let uu____12552 =
                FStar_All.pipe_right quals (FStar_Util.for_some has_eq)  in
              if uu____12552 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_assume uu____12556 ->
              let uu____12563 =
                let uu____12564 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (visibility x) ||
                            (x = FStar_Syntax_Syntax.Assumption)))
                   in
                Prims.op_Negation uu____12564  in
              if uu____12563 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect uu____12570 ->
              let uu____12571 =
                let uu____12572 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12572  in
              if uu____12571 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12578 ->
              let uu____12579 =
                let uu____12580 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  ->
                          (((x = FStar_Syntax_Syntax.TotalEffect) ||
                              (inferred x))
                             || (visibility x))
                            || (reification x)))
                   in
                Prims.op_Negation uu____12580  in
              if uu____12579 then err'1 () else ()
          | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12586 ->
              let uu____12599 =
                let uu____12600 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_all
                       (fun x  -> (inferred x) || (visibility x)))
                   in
                Prims.op_Negation uu____12600  in
              if uu____12599 then err'1 () else ()
          | uu____12606 -> ()))
      else ()
  
let (must_erase_for_extraction :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g  ->
    fun t  ->
      let rec aux_whnf env t1 =
        let uu____12640 =
          let uu____12641 = FStar_Syntax_Subst.compress t1  in
          uu____12641.FStar_Syntax_Syntax.n  in
        match uu____12640 with
        | FStar_Syntax_Syntax.Tm_type uu____12644 -> true
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
              (let uu____12647 =
                 let uu____12652 =
                   FStar_All.pipe_right fv FStar_Syntax_Syntax.lid_of_fv  in
                 FStar_All.pipe_right uu____12652
                   (FStar_TypeChecker_Env.lookup_attrs_of_lid g)
                  in
               FStar_All.pipe_right uu____12647
                 (fun l_opt  ->
                    (FStar_Util.is_some l_opt) &&
                      (let uu____12670 =
                         FStar_All.pipe_right l_opt FStar_Util.must  in
                       FStar_All.pipe_right uu____12670
                         (FStar_List.existsb
                            (fun t2  ->
                               let uu____12687 =
                                 let uu____12688 =
                                   FStar_Syntax_Subst.compress t2  in
                                 uu____12688.FStar_Syntax_Syntax.n  in
                               match uu____12687 with
                               | FStar_Syntax_Syntax.Tm_fvar fv1 when
                                   FStar_Ident.lid_equals
                                     (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     FStar_Parser_Const.must_erase_for_extraction_attr
                                   -> true
                               | uu____12692 -> false)))))
        | FStar_Syntax_Syntax.Tm_arrow uu____12693 ->
            let uu____12706 = FStar_Syntax_Util.arrow_formals_comp t1  in
            (match uu____12706 with
             | (bs,c) ->
                 let env1 = FStar_TypeChecker_Env.push_binders env bs  in
                 let uu____12732 = FStar_Syntax_Util.is_pure_comp c  in
                 if uu____12732
                 then aux env1 (FStar_Syntax_Util.comp_result c)
                 else FStar_Syntax_Util.is_pure_or_ghost_comp c)
        | FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____12734;
               FStar_Syntax_Syntax.index = uu____12735;
               FStar_Syntax_Syntax.sort = t2;_},uu____12737)
            -> aux env t2
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____12745,uu____12746) ->
            aux env t2
        | FStar_Syntax_Syntax.Tm_app (head1,uu____12788::[]) ->
            let uu____12819 =
              let uu____12820 = FStar_Syntax_Util.un_uinst head1  in
              uu____12820.FStar_Syntax_Syntax.n  in
            (match uu____12819 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.erased_lid
             | uu____12824 -> false)
        | uu____12825 -> false
      
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
        (let uu____12833 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Extraction")
            in
         if uu____12833
         then
           let uu____12834 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "must_erase=%s: %s\n"
             (if res then "true" else "false") uu____12834
         else ());
        res
       in aux g t
  