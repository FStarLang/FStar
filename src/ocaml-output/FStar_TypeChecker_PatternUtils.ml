open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
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
            let uu____84 =
              let uu____89 =
                FStar_Syntax_Subst.compress x.FStar_Syntax_Syntax.sort  in
              match uu____89 with
              | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
                  FStar_Syntax_Syntax.pos = uu____94;
                  FStar_Syntax_Syntax.vars = uu____95;_} ->
                  let uu____98 = FStar_Syntax_Util.type_u ()  in
                  (match uu____98 with
                   | (t,uu____108) ->
                       let uu____109 =
                         let uu____122 = FStar_Syntax_Syntax.range_of_bv x
                            in
                         FStar_TypeChecker_Env.new_implicit_var_aux
                           "pattern bv type" uu____122 env1 t
                           FStar_Syntax_Syntax.Allow_untyped
                          in
                       (match uu____109 with | (t1,uu____128,g) -> (t1, g)))
              | t -> tc_annot env1 t  in
            match uu____84 with
            | (t_x,guard) ->
                ((let uu___292_150 = x  in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (uu___292_150.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (uu___292_150.FStar_Syntax_Syntax.index);
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
                  | uu____225 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____233) ->
                let uu____238 = FStar_Syntax_Util.type_u ()  in
                (match uu____238 with
                 | (k,uu____264) ->
                     let uu____265 =
                       let uu____278 = FStar_Syntax_Syntax.range_of_bv x  in
                       FStar_TypeChecker_Env.new_implicit_var_aux
                         "pat_dot_term type" uu____278 env1 k
                         FStar_Syntax_Syntax.Allow_untyped
                        in
                     (match uu____265 with
                      | (t,uu____300,g) ->
                          let x1 =
                            let uu___293_315 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___293_315.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___293_315.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____316 =
                            let uu____329 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            FStar_TypeChecker_Env.new_implicit_var_aux
                              "pat_dot_term" uu____329 env1 t
                              FStar_Syntax_Syntax.Allow_untyped
                             in
                          (match uu____316 with
                           | (e,uu____351,g') ->
                               let p2 =
                                 let uu___294_368 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___294_368.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____371 =
                                 FStar_TypeChecker_Env.conj_guard g g'  in
                               ([], [], [], env1, e, uu____371, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____379 = check_bv env1 x  in
                (match uu____379 with
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
                let uu____418 = check_bv env1 x  in
                (match uu____418 with
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
                let uu____473 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____607  ->
                          fun uu____608  ->
                            match (uu____607, uu____608) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____806 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____806 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____882 =
                                       FStar_TypeChecker_Env.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____882, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Env.trivial_guard, []))
                   in
                (match uu____473 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____1013 =
                         let uu____1018 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____1019 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____1018 uu____1019
                          in
                       uu____1013 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1040 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1051 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1062 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1040, uu____1051, uu____1062, env2, e, guard,
                       (let uu___295_1080 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___295_1080.FStar_Syntax_Syntax.p)
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
                    (fun uu____1178  ->
                       match uu____1178 with
                       | (p2,imp) ->
                           let uu____1197 = elaborate_pat env1 p2  in
                           (uu____1197, imp)) pats
                   in
                let uu____1202 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____1202 with
                 | (uu____1209,t) ->
                     let uu____1211 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____1211 with
                      | (f,uu____1229) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____1359::uu____1360) ->
                                let uu____1403 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____1403
                            | (uu____1412::uu____1413,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____1491  ->
                                        match uu____1491 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____1518 =
                                                     let uu____1521 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____1521
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____1518
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____1523 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____1523, true)
                                             | uu____1528 ->
                                                 let uu____1531 =
                                                   let uu____1536 =
                                                     let uu____1537 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1537
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____1536)
                                                    in
                                                 let uu____1538 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1531 uu____1538)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____1612,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____1613)) when p_imp ->
                                     let uu____1616 = aux formals' pats'  in
                                     (p2, true) :: uu____1616
                                 | (uu____1633,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____1641 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____1641
                                        in
                                     let uu____1642 = aux formals' pats2  in
                                     (p3, true) :: uu____1642
                                 | (uu____1659,imp) ->
                                     let uu____1665 =
                                       let uu____1672 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____1672)  in
                                     let uu____1675 = aux formals' pats'  in
                                     uu____1665 :: uu____1675)
                             in
                          let uu___296_1690 = p1  in
                          let uu____1693 =
                            let uu____1694 =
                              let uu____1707 = aux f pats1  in
                              (fv, uu____1707)  in
                            FStar_Syntax_Syntax.Pat_cons uu____1694  in
                          {
                            FStar_Syntax_Syntax.v = uu____1693;
                            FStar_Syntax_Syntax.p =
                              (uu___296_1690.FStar_Syntax_Syntax.p)
                          }))
            | uu____1724 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____1766 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____1766 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____1824 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____1824 with
                 | FStar_Pervasives_Native.Some x ->
                     let m = FStar_Syntax_Print.bv_to_string x  in
                     let err =
                       let uu____1856 =
                         FStar_Util.format1
                           "The pattern variable \"%s\" was used more than once"
                           m
                          in
                       (FStar_Errors.Fatal_NonLinearPatternVars, uu____1856)
                        in
                     FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
                 | uu____1875 -> (b, a, w, arg, guard, p3))
             in
          let uu____1884 = one_pat true env p  in
          match uu____1884 with
          | (b,uu____1914,uu____1915,tm,guard,p1) -> (b, tm, guard, p1)
  