open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let rec (elaborate_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat -> FStar_Syntax_Syntax.pat)
  =
  fun env  ->
    fun p  ->
      let maybe_dot inaccessible a r =
        if inaccessible
        then
          FStar_Syntax_Syntax.withinfo
            (FStar_Syntax_Syntax.Pat_dot_term (a, FStar_Syntax_Syntax.tun)) r
        else FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a) r
         in
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
          let pats1 =
            FStar_List.map
              (fun uu____77  ->
                 match uu____77 with
                 | (p1,imp) ->
                     let uu____88 = elaborate_pat env p1  in (uu____88, imp))
              pats
             in
          let uu____89 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____89 with
           | (uu____94,t) ->
               let uu____96 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____96 with
                | (f,uu____112) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____242::uu____243) ->
                          let uu____286 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____286
                      | (uu____295::uu____296,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____374  ->
                                  match uu____374 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____401 =
                                               let uu____404 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____404
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____401
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____406 =
                                             maybe_dot inaccessible a r  in
                                           (uu____406, true)
                                       | uu____411 ->
                                           let uu____414 =
                                             let uu____419 =
                                               let uu____420 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____420
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____419)
                                              in
                                           let uu____421 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error uu____414
                                             uu____421)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____495,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____496)) when
                               p_imp ->
                               let uu____499 = aux formals' pats'  in
                               (p1, true) :: uu____499
                           | (uu____516,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____524 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____524  in
                               let uu____525 = aux formals' pats2  in
                               (p2, true) :: uu____525
                           | (uu____542,imp) ->
                               let uu____548 =
                                 let uu____555 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____555)  in
                               let uu____558 = aux formals' pats'  in
                               uu____548 :: uu____558)
                       in
                    let uu___251_573 = p  in
                    let uu____574 =
                      let uu____575 =
                        let uu____588 = aux f pats1  in (fv, uu____588)  in
                      FStar_Syntax_Syntax.Pat_cons uu____575  in
                    {
                      FStar_Syntax_Syntax.v = uu____574;
                      FStar_Syntax_Syntax.p =
                        (uu___251_573.FStar_Syntax_Syntax.p)
                    }))
      | uu____605 -> p
  
let (pat_as_exp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.pat) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun p  ->
      let check_bv env1 x =
        let uu____655 = FStar_Syntax_Util.type_u ()  in
        match uu____655 with
        | (t,uu____665) ->
            let uu____666 =
              let uu____679 = FStar_Syntax_Syntax.range_of_bv x  in
              FStar_TypeChecker_Env.new_implicit_var_aux "pattern bv type"
                uu____679 env1 t FStar_Syntax_Syntax.Allow_untyped
               in
            (match uu____666 with
             | (t_x,uu____685,guard) ->
                 ((let uu___252_700 = x  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___252_700.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___252_700.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = t_x
                   }), guard))
         in
      let rec pat_as_arg_with_env env1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant c ->
            let e =
              match c with
              | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw)
                  ->
                  FStar_ToSyntax_ToSyntax.desugar_machine_integer
                    env1.FStar_TypeChecker_Env.dsenv repr sw
                    p1.FStar_Syntax_Syntax.p
              | uu____770 ->
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
                    FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
               in
            ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
        | FStar_Syntax_Syntax.Pat_dot_term (x,uu____778) ->
            let uu____783 = FStar_Syntax_Util.type_u ()  in
            (match uu____783 with
             | (k,uu____809) ->
                 let uu____810 =
                   let uu____823 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pat_dot_term type" uu____823 env1 k
                     FStar_Syntax_Syntax.Allow_untyped
                    in
                 (match uu____810 with
                  | (t,uu____845,g) ->
                      let x1 =
                        let uu___253_860 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___253_860.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___253_860.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t
                        }  in
                      let uu____861 =
                        let uu____874 = FStar_Syntax_Syntax.range_of_bv x1
                           in
                        FStar_TypeChecker_Env.new_implicit_var_aux
                          "pat_dot_term" uu____874 env1 t
                          FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____861 with
                       | (e,uu____896,g') ->
                           let p2 =
                             let uu___254_913 = p1  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                               FStar_Syntax_Syntax.p =
                                 (uu___254_913.FStar_Syntax_Syntax.p)
                             }  in
                           let uu____916 =
                             FStar_TypeChecker_Env.conj_guard g g'  in
                           ([], [], [], env1, e, uu____916, p2))))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let uu____924 = check_bv env1 x  in
            (match uu____924 with
             | (x1,g) ->
                 let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                 let e =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                     FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                    in
                 ([x1], [], [x1], env2, e, g, p1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let uu____962 = check_bv env1 x  in
            (match uu____962 with
             | (x1,g) ->
                 let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                 let e =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                     FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                    in
                 ([x1], [x1], [], env2, e, g, p1))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____1017 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____1151  ->
                      fun uu____1152  ->
                        match (uu____1151, uu____1152) with
                        | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                            let uu____1350 = pat_as_arg_with_env env2 p2  in
                            (match uu____1350 with
                             | (b',a',w',env3,te,guard',pat) ->
                                 let arg =
                                   if imp
                                   then FStar_Syntax_Syntax.iarg te
                                   else FStar_Syntax_Syntax.as_arg te  in
                                 let uu____1426 =
                                   FStar_TypeChecker_Env.conj_guard guard
                                     guard'
                                    in
                                 ((b' :: b), (a' :: a), (w' :: w), env3, (arg
                                   :: args), uu____1426, ((pat, imp) ::
                                   pats1))))
                   ([], [], [], env1, [],
                     FStar_TypeChecker_Env.trivial_guard, []))
               in
            (match uu____1017 with
             | (b,a,w,env2,args,guard,pats1) ->
                 let e =
                   let uu____1557 =
                     let uu____1562 = FStar_Syntax_Syntax.fv_to_tm fv  in
                     let uu____1563 =
                       FStar_All.pipe_right args FStar_List.rev  in
                     FStar_Syntax_Syntax.mk_Tm_app uu____1562 uu____1563  in
                   uu____1557 FStar_Pervasives_Native.None
                     p1.FStar_Syntax_Syntax.p
                    in
                 let uu____1568 =
                   FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten
                    in
                 let uu____1579 =
                   FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten
                    in
                 let uu____1590 =
                   FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten
                    in
                 (uu____1568, uu____1579, uu____1590, env2, e, guard,
                   (let uu___255_1608 = p1  in
                    {
                      FStar_Syntax_Syntax.v =
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv, (FStar_List.rev pats1)));
                      FStar_Syntax_Syntax.p =
                        (uu___255_1608.FStar_Syntax_Syntax.p)
                    })))
         in
      let one_pat env1 p1 =
        let p2 = elaborate_pat env1 p1  in
        let uu____1651 = pat_as_arg_with_env env1 p2  in
        match uu____1651 with
        | (b,a,w,env2,arg,guard,p3) ->
            let uu____1709 =
              FStar_All.pipe_right b
                (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
               in
            (match uu____1709 with
             | FStar_Pervasives_Native.Some x ->
                 let m = FStar_Syntax_Print.bv_to_string x  in
                 let err =
                   let uu____1741 =
                     FStar_Util.format1
                       "The pattern variable \"%s\" was used more than once"
                       m
                      in
                   (FStar_Errors.Fatal_NonLinearPatternVars, uu____1741)  in
                 FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
             | uu____1760 -> (b, a, w, arg, guard, p3))
         in
      let uu____1769 = one_pat env p  in
      match uu____1769 with
      | (b,uu____1799,uu____1800,tm,guard,p1) -> (b, tm, guard, p1)
  