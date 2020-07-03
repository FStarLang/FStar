open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
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
              (fun uu____76 ->
                 match uu____76 with
                 | (p1, imp) ->
                     let uu____87 = elaborate_pat env p1 in (uu____87, imp))
              pats in
          let uu____88 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____88 with
           | (uu____93, t) ->
               let uu____95 = FStar_Syntax_Util.arrow_formals t in
               (match uu____95 with
                | (f, uu____103) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([], []) -> []
                      | ([], uu____217::uu____218) ->
                          let uu____261 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____261
                      | (uu____270::uu____271, []) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____349 ->
                                  match uu____349 with
                                  | (t1, imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____376 =
                                               let uu____379 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1 in
                                               FStar_Pervasives_Native.Some
                                                 uu____379 in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____376
                                               FStar_Syntax_Syntax.tun in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let uu____381 =
                                             maybe_dot inaccessible a r in
                                           (uu____381, true)
                                       | uu____386 ->
                                           let uu____389 =
                                             let uu____394 =
                                               let uu____395 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____395 in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____394) in
                                           let uu____396 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           FStar_Errors.raise_error uu____389
                                             uu____396)))
                      | (f1::formals', (p1, p_imp)::pats') ->
                          (match f1 with
                           | (uu____470, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____482
                                    ->
                                    let uu____489 = aux formals' pats' in
                                    (p1, true) :: uu____489
                                | FStar_Syntax_Syntax.Pat_wild uu____506 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun in
                                    let p2 =
                                      let uu____511 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      maybe_dot inaccessible a uu____511 in
                                    let uu____512 = aux formals' pats' in
                                    (p2, true) :: uu____512
                                | uu____529 ->
                                    let uu____530 =
                                      let uu____535 =
                                        let uu____536 =
                                          FStar_Syntax_Print.pat_to_string p1 in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____536 in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____535) in
                                    FStar_Errors.raise_error uu____530
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____545, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____546)) when
                               p_imp ->
                               let uu____549 = aux formals' pats' in
                               (p1, true) :: uu____549
                           | (uu____566, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun in
                               let p2 =
                                 let uu____574 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 maybe_dot inaccessible a uu____574 in
                               let uu____575 = aux formals' pats2 in
                               (p2, true) :: uu____575
                           | (uu____592, imp) ->
                               let uu____598 =
                                 let uu____605 =
                                   FStar_Syntax_Syntax.is_implicit imp in
                                 (p1, uu____605) in
                               let uu____608 = aux formals' pats' in
                               uu____598 :: uu____608) in
                    let uu___82_623 = p in
                    let uu____624 =
                      let uu____625 =
                        let uu____638 = aux f pats1 in (fv, uu____638) in
                      FStar_Syntax_Syntax.Pat_cons uu____625 in
                    {
                      FStar_Syntax_Syntax.v = uu____624;
                      FStar_Syntax_Syntax.p =
                        (uu___82_623.FStar_Syntax_Syntax.p)
                    }))
      | uu____655 -> p
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.pat))
  =
  fun introduce_bv_uvars ->
    fun env ->
      fun p ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___95_715 = x in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_715.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_715.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____717 = FStar_Syntax_Util.type_u () in
             match uu____717 with
             | (t, uu____729) ->
                 let uu____730 =
                   let uu____743 = FStar_Syntax_Syntax.range_of_bv x in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____743 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None in
                 (match uu____730 with
                  | (t_x, uu____751, guard) ->
                      let x1 =
                        let uu___104_766 = x in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___104_766.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___104_766.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        } in
                      let uu____767 = FStar_TypeChecker_Env.push_bv env1 x1 in
                      (x1, guard, uu____767))) in
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
                | uu____837 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      p1.FStar_Syntax_Syntax.p in
              ([], [], [], env1, e, FStar_TypeChecker_Common.trivial_guard,
                p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x, uu____845) ->
              let uu____850 = FStar_Syntax_Util.type_u () in
              (match uu____850 with
               | (k, uu____876) ->
                   let uu____877 =
                     let uu____890 = FStar_Syntax_Syntax.range_of_bv x in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____890 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None in
                   (match uu____877 with
                    | (t, uu____912, g) ->
                        let x1 =
                          let uu___130_927 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_927.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_927.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          } in
                        let uu____928 =
                          let uu____941 = FStar_Syntax_Syntax.range_of_bv x1 in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____941 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None in
                        (match uu____928 with
                         | (e, uu____963, g') ->
                             let p2 =
                               let uu___137_980 = p1 in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___137_980.FStar_Syntax_Syntax.p)
                               } in
                             let uu____983 =
                               FStar_TypeChecker_Common.conj_guard g g' in
                             ([], [], [], env1, e, uu____983, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____991 = intro_bv env1 x in
              (match uu____991 with
               | (x1, g, env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       p1.FStar_Syntax_Syntax.p in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1031 = intro_bv env1 x in
              (match uu____1031 with
               | (x1, g, env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       p1.FStar_Syntax_Syntax.p in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
              let uu____1088 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1222 ->
                        fun uu____1223 ->
                          match (uu____1222, uu____1223) with
                          | ((b, a, w, env2, args, guard, pats1), (p2, imp))
                              ->
                              let uu____1421 = pat_as_arg_with_env env2 p2 in
                              (match uu____1421 with
                               | (b', a', w', env3, te, guard', pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te in
                                   let uu____1497 =
                                     FStar_TypeChecker_Common.conj_guard
                                       guard guard' in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1497, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Common.trivial_guard, [])) in
              (match uu____1088 with
               | (b, a, w, env2, args, guard, pats1) ->
                   let e =
                     let uu____1626 = FStar_Syntax_Syntax.fv_to_tm fv in
                     let uu____1627 =
                       FStar_All.pipe_right args FStar_List.rev in
                     FStar_Syntax_Syntax.mk_Tm_app uu____1626 uu____1627
                       p1.FStar_Syntax_Syntax.p in
                   let uu____1630 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten in
                   let uu____1641 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten in
                   let uu____1652 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten in
                   (uu____1630, uu____1641, uu____1652, env2, e, guard,
                     (let uu___188_1670 = p1 in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___188_1670.FStar_Syntax_Syntax.p)
                      }))) in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1 in
          let uu____1713 = pat_as_arg_with_env env1 p2 in
          match uu____1713 with
          | (b, a, w, env2, arg, guard, p3) ->
              let uu____1771 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
              (match uu____1771 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x in
                   let err =
                     let uu____1803 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1803) in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1822 -> (b, a, w, arg, guard, p3)) in
        let uu____1831 = one_pat env p in
        match uu____1831 with
        | (b, uu____1861, uu____1862, tm, guard, p1) -> (b, tm, guard, p1)