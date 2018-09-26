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
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____507
                                    ->
                                    let uu____514 = aux formals' pats'  in
                                    (p1, true) :: uu____514
                                | FStar_Syntax_Syntax.Pat_wild uu____531 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____536 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____536  in
                                    let uu____537 = aux formals' pats'  in
                                    (p2, true) :: uu____537
                                | uu____554 ->
                                    let uu____555 =
                                      let uu____560 =
                                        let uu____561 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____561
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____560)
                                       in
                                    FStar_Errors.raise_error uu____555
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____570,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____571)) when
                               p_imp ->
                               let uu____574 = aux formals' pats'  in
                               (p1, true) :: uu____574
                           | (uu____591,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____599 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____599  in
                               let uu____600 = aux formals' pats2  in
                               (p2, true) :: uu____600
                           | (uu____617,imp) ->
                               let uu____623 =
                                 let uu____630 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____630)  in
                               let uu____633 = aux formals' pats'  in
                               uu____623 :: uu____633)
                       in
                    let uu___265_648 = p  in
                    let uu____649 =
                      let uu____650 =
                        let uu____663 = aux f pats1  in (fv, uu____663)  in
                      FStar_Syntax_Syntax.Pat_cons uu____650  in
                    {
                      FStar_Syntax_Syntax.v = uu____649;
                      FStar_Syntax_Syntax.p =
                        (uu___265_648.FStar_Syntax_Syntax.p)
                    }))
      | uu____680 -> p
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.pat) FStar_Pervasives_Native.tuple4)
  =
  fun introduce_bv_uvars  ->
    fun env  ->
      fun p  ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___266_740 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___266_740.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___266_740.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____742 = FStar_Syntax_Util.type_u ()  in
             match uu____742 with
             | (t,uu____754) ->
                 let uu____755 =
                   let uu____768 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____768 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                    in
                 (match uu____755 with
                  | (t_x,uu____776,guard) ->
                      let x1 =
                        let uu___267_791 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___267_791.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___267_791.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____792 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____792)))
           in
        let rec pat_as_arg_with_env env1 p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let e =
                match c with
                | FStar_Const.Const_int
                    (repr,FStar_Pervasives_Native.Some sw) ->
                    FStar_ToSyntax_ToSyntax.desugar_machine_integer
                      env1.FStar_TypeChecker_Env.dsenv repr sw
                      p1.FStar_Syntax_Syntax.p
                | uu____862 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____870) ->
              let uu____875 = FStar_Syntax_Util.type_u ()  in
              (match uu____875 with
               | (k,uu____901) ->
                   let uu____902 =
                     let uu____915 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____915 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                      in
                   (match uu____902 with
                    | (t,uu____937,g) ->
                        let x1 =
                          let uu___268_952 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___268_952.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___268_952.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____953 =
                          let uu____966 = FStar_Syntax_Syntax.range_of_bv x1
                             in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____966 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                           in
                        (match uu____953 with
                         | (e,uu____988,g') ->
                             let p2 =
                               let uu___269_1005 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___269_1005.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____1008 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____1008, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1016 = intro_bv env1 x  in
              (match uu____1016 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1056 = intro_bv env1 x  in
              (match uu____1056 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1113 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1247  ->
                        fun uu____1248  ->
                          match (uu____1247, uu____1248) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____1446 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____1446 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____1522 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1522, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____1113 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____1653 =
                       let uu____1658 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____1659 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____1658 uu____1659
                        in
                     uu____1653 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____1664 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1675 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1686 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1664, uu____1675, uu____1686, env2, e, guard,
                     (let uu___270_1704 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___270_1704.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1747 = pat_as_arg_with_env env1 p2  in
          match uu____1747 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____1805 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1805 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____1837 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1837)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1856 -> (b, a, w, arg, guard, p3))
           in
        let uu____1865 = one_pat env p  in
        match uu____1865 with
        | (b,uu____1895,uu____1896,tm,guard,p1) -> (b, tm, guard, p1)
  