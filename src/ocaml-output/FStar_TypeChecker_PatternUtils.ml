open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_Syntax_Syntax.lcomp)
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
              (fun uu____55137  ->
                 match uu____55137 with
                 | (p1,imp) ->
                     let uu____55152 = elaborate_pat env p1  in
                     (uu____55152, imp)) pats
             in
          let uu____55154 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____55154 with
           | (uu____55159,t) ->
               let uu____55161 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____55161 with
                | (f,uu____55177) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____55315::uu____55316) ->
                          let uu____55363 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____55363
                      | (uu____55375::uu____55376,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____55458  ->
                                  match uu____55458 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____55488 =
                                               let uu____55491 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____55491
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____55488
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____55493 =
                                             maybe_dot inaccessible a r  in
                                           (uu____55493, true)
                                       | uu____55500 ->
                                           let uu____55503 =
                                             let uu____55509 =
                                               let uu____55511 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____55511
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____55509)
                                              in
                                           let uu____55515 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____55503 uu____55515)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____55596,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____55610 ->
                                    let uu____55617 = aux formals' pats'  in
                                    (p1, true) :: uu____55617
                                | FStar_Syntax_Syntax.Pat_wild uu____55638 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____55643 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____55643
                                       in
                                    let uu____55644 = aux formals' pats'  in
                                    (p2, true) :: uu____55644
                                | uu____55665 ->
                                    let uu____55666 =
                                      let uu____55672 =
                                        let uu____55674 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____55674
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____55672)
                                       in
                                    FStar_Errors.raise_error uu____55666
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____55687,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____55688))
                               when p_imp ->
                               let uu____55692 = aux formals' pats'  in
                               (p1, true) :: uu____55692
                           | (uu____55713,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____55722 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____55722  in
                               let uu____55723 = aux formals' pats2  in
                               (p2, true) :: uu____55723
                           | (uu____55744,imp) ->
                               let uu____55750 =
                                 let uu____55758 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____55758)  in
                               let uu____55763 = aux formals' pats'  in
                               uu____55750 :: uu____55763)
                       in
                    let uu___598_55780 = p  in
                    let uu____55781 =
                      let uu____55782 =
                        let uu____55796 = aux f pats1  in (fv, uu____55796)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____55782  in
                    {
                      FStar_Syntax_Syntax.v = uu____55781;
                      FStar_Syntax_Syntax.p =
                        (uu___598_55780.FStar_Syntax_Syntax.p)
                    }))
      | uu____55815 -> p
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.pat))
  =
  fun introduce_bv_uvars  ->
    fun env  ->
      fun p  ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___611_55879 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_55879.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_55879.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____55882 = FStar_Syntax_Util.type_u ()  in
             match uu____55882 with
             | (t,uu____55894) ->
                 let uu____55895 =
                   let uu____55908 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____55908 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____55895 with
                  | (t_x,uu____55921,guard) ->
                      let x1 =
                        let uu___620_55936 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_55936.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_55936.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____55937 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____55937)))
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
                | uu____56009 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____56017) ->
              let uu____56022 = FStar_Syntax_Util.type_u ()  in
              (match uu____56022 with
               | (k,uu____56048) ->
                   let uu____56049 =
                     let uu____56062 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____56062 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____56049 with
                    | (t,uu____56089,g) ->
                        let x1 =
                          let uu___646_56104 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_56104.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_56104.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____56105 =
                          let uu____56118 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____56118 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____56105 with
                         | (e,uu____56145,g') ->
                             let p2 =
                               let uu___653_56162 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_56162.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____56165 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____56165, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____56173 = intro_bv env1 x  in
              (match uu____56173 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____56213 = intro_bv env1 x  in
              (match uu____56213 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____56272 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____56411  ->
                        fun uu____56412  ->
                          match (uu____56411, uu____56412) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____56621 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____56621 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____56700 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____56700, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____56272 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____56838 =
                       let uu____56843 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____56844 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____56843 uu____56844
                        in
                     uu____56838 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____56847 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____56858 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____56869 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____56847, uu____56858, uu____56869, env2, e, guard,
                     (let uu___704_56887 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_56887.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____56932 = pat_as_arg_with_env env1 p2  in
          match uu____56932 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____56990 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____56990 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____57024 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____57024)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____57046 -> (b, a, w, arg, guard, p3))
           in
        let uu____57055 = one_pat env p  in
        match uu____57055 with
        | (b,uu____57085,uu____57086,tm,guard,p1) -> (b, tm, guard, p1)
  