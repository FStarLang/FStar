open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
let rec (elaborate_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat -> FStar_Syntax_Syntax.pat)
  =
  fun env ->
    fun p ->
      let maybe_dot inaccessible a r =
        if inaccessible
        then
          FStar_Syntax_Syntax.withinfo
            (FStar_Syntax_Syntax.Pat_dot_term (a, FStar_Syntax_Syntax.tun)) r
        else FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a) r in
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let pats1 =
            FStar_List.map
              (fun uu____85 ->
                 match uu____85 with
                 | (p1, imp) ->
                     let uu____100 = elaborate_pat env p1 in (uu____100, imp))
              pats in
          let uu____102 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____102 with
           | (uu____107, t) ->
               let uu____109 = FStar_Syntax_Util.arrow_formals t in
               (match uu____109 with
                | (f, uu____125) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([], []) -> []
                      | ([], uu____263::uu____264) ->
                          let uu____311 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____311
                      | (uu____323::uu____324, []) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____406 ->
                                  match uu____406 with
                                  | (t1, imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____436 =
                                               let uu____439 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1 in
                                               FStar_Pervasives_Native.Some
                                                 uu____439 in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____436
                                               FStar_Syntax_Syntax.tun in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let uu____441 =
                                             maybe_dot inaccessible a r in
                                           (uu____441, true)
                                       | uu____448 ->
                                           let uu____451 =
                                             let uu____457 =
                                               let uu____459 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____459 in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____457) in
                                           let uu____463 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           FStar_Errors.raise_error uu____451
                                             uu____463)))
                      | (f1::formals', (p1, p_imp)::pats') ->
                          (match f1 with
                           | (uu____544, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____558
                                    ->
                                    let uu____565 = aux formals' pats' in
                                    (p1, true) :: uu____565
                                | FStar_Syntax_Syntax.Pat_wild uu____586 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun in
                                    let p2 =
                                      let uu____591 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      maybe_dot inaccessible a uu____591 in
                                    let uu____592 = aux formals' pats' in
                                    (p2, true) :: uu____592
                                | uu____613 ->
                                    let uu____614 =
                                      let uu____620 =
                                        let uu____622 =
                                          FStar_Syntax_Print.pat_to_string p1 in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____622 in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____620) in
                                    FStar_Errors.raise_error uu____614
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____635, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____636)) when
                               p_imp ->
                               let uu____640 = aux formals' pats' in
                               (p1, true) :: uu____640
                           | (uu____661, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun in
                               let p2 =
                                 let uu____670 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 maybe_dot inaccessible a uu____670 in
                               let uu____671 = aux formals' pats2 in
                               (p2, true) :: uu____671
                           | (uu____692, imp) ->
                               let uu____698 =
                                 let uu____706 =
                                   FStar_Syntax_Syntax.is_implicit imp in
                                 (p1, uu____706) in
                               let uu____711 = aux formals' pats' in
                               uu____698 :: uu____711) in
                    let uu___82_728 = p in
                    let uu____729 =
                      let uu____730 =
                        let uu____744 = aux f pats1 in (fv, uu____744) in
                      FStar_Syntax_Syntax.Pat_cons uu____730 in
                    {
                      FStar_Syntax_Syntax.v = uu____729;
                      FStar_Syntax_Syntax.p =
                        (uu___82_728.FStar_Syntax_Syntax.p)
                    }))
      | uu____763 -> p
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat))
  =
  fun introduce_bv_uvars ->
    fun env ->
      fun p ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___95_827 = x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_827.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_827.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____830 = FStar_Syntax_Util.type_u () in
             match uu____830 with
             | (t, uu____842) ->
                 let uu____843 =
                   let uu____856 = FStar_Syntax_Syntax.range_of_bv x in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____856 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None in
                 (match uu____843 with
                  | (t_x, uu____869, guard) ->
                      let x1 =
                        let uu___104_884 = x in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___104_884.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___104_884.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        } in
                      let uu____885 = FStar_TypeChecker_Env.push_bv env1 x1 in
                      (x1, guard, uu____885))) in
        let rec pat_as_arg_with_env env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                match c with
                | FStar_Const.Const_int
                    (repr, FStar_Pervasives_Native.Some sw) ->
                    FStar_ToSyntax_ToSyntax.desugar_machine_integer
                      env1.FStar_TypeChecker_Env.dsenv repr sw
                      p1.FStar_Syntax_Syntax.p
                | uu____957 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x, uu____965) ->
              let uu____970 = FStar_Syntax_Util.type_u () in
              (match uu____970 with
               | (k, uu____996) ->
                   let uu____997 =
                     let uu____1010 = FStar_Syntax_Syntax.range_of_bv x in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____1010 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None in
                   (match uu____997 with
                    | (t, uu____1037, g) ->
                        let x1 =
                          let uu___130_1052 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_1052.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_1052.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          } in
                        let uu____1053 =
                          let uu____1066 = FStar_Syntax_Syntax.range_of_bv x1 in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____1066 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None in
                        (match uu____1053 with
                         | (e, uu____1093, g') ->
                             let p2 =
                               let uu___137_1110 = p1 in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___137_1110.FStar_Syntax_Syntax.p)
                               } in
                             let uu____1113 =
                               FStar_TypeChecker_Env.conj_guard g g' in
                             ([], [], [], env1, e, uu____1113, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1121 = intro_bv env1 x in
              (match uu____1121 with
               | (x1, g, env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1161 = intro_bv env1 x in
              (match uu____1161 with
               | (x1, g, env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu____1220 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1359 ->
                        fun uu____1360 ->
                          match (uu____1359, uu____1360) with
                          | ((b, a, w, env2, args, guard, pats1), (p2, imp))
                              ->
                              let uu____1569 = pat_as_arg_with_env env2 p2 in
                              (match uu____1569 with
                               | (b', a', w', env3, te, guard', pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   let uu____1648 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard' in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1648, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, [])) in
              (match uu____1220 with
               | (b, a, w, env2, args, guard, pats1) ->
                   let e =
                     let uu____1786 =
                       let uu____1791 = FStar_Syntax_Syntax.fv_to_tm fv in
                       let uu____1792 =
                         FStar_All.pipe_right args FStar_List.rev in
                       FStar_Syntax_Syntax.mk_Tm_app uu____1791 uu____1792 in
                     uu____1786 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1795 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1806 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1817 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1795, uu____1806, uu____1817, env2, e, guard,
                     (let uu___188_1835 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___188_1835.FStar_Syntax_Syntax.p)
                      }))) in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1880 = pat_as_arg_with_env env1 p2 in
          match uu____1880 with
          | (b, a, w, env2, arg, guard, p3) ->
              let uu____1938 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1938 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x in
                   let err =
                     let uu____1972 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1972) in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1994 -> (b, a, w, arg, guard, p3)) in
        let uu____2003 = one_pat env p in
        match uu____2003 with
        | (b, uu____2033, uu____2034, tm, guard, p1) -> (b, tm, guard, p1)