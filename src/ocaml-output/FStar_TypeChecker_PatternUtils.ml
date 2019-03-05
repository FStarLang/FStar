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
              (fun uu____59809  ->
                 match uu____59809 with
                 | (p1,imp) ->
                     let uu____59824 = elaborate_pat env p1  in
                     (uu____59824, imp)) pats
             in
          let uu____59826 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59826 with
           | (uu____59831,t) ->
               let uu____59833 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59833 with
                | (f,uu____59849) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59987::uu____59988) ->
                          let uu____60035 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____60035
                      | (uu____60047::uu____60048,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60130  ->
                                  match uu____60130 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60160 =
                                               let uu____60163 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60163
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60160
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60165 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60165, true)
                                       | uu____60172 ->
                                           let uu____60175 =
                                             let uu____60181 =
                                               let uu____60183 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60183
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60181)
                                              in
                                           let uu____60187 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60175 uu____60187)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60268,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60282 ->
                                    let uu____60289 = aux formals' pats'  in
                                    (p1, true) :: uu____60289
                                | FStar_Syntax_Syntax.Pat_wild uu____60310 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60315 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60315
                                       in
                                    let uu____60316 = aux formals' pats'  in
                                    (p2, true) :: uu____60316
                                | uu____60337 ->
                                    let uu____60338 =
                                      let uu____60344 =
                                        let uu____60346 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60346
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60344)
                                       in
                                    FStar_Errors.raise_error uu____60338
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60359,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60360))
                               when p_imp ->
                               let uu____60364 = aux formals' pats'  in
                               (p1, true) :: uu____60364
                           | (uu____60385,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60394 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60394  in
                               let uu____60395 = aux formals' pats2  in
                               (p2, true) :: uu____60395
                           | (uu____60416,imp) ->
                               let uu____60422 =
                                 let uu____60430 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60430)  in
                               let uu____60435 = aux formals' pats'  in
                               uu____60422 :: uu____60435)
                       in
                    let uu___598_60452 = p  in
                    let uu____60453 =
                      let uu____60454 =
                        let uu____60468 = aux f pats1  in (fv, uu____60468)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60454  in
                    {
                      FStar_Syntax_Syntax.v = uu____60453;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60452.FStar_Syntax_Syntax.p)
                    }))
      | uu____60487 -> p
  
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
            ((let uu___611_60551 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60551.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60551.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60554 = FStar_Syntax_Util.type_u ()  in
             match uu____60554 with
             | (t,uu____60566) ->
                 let uu____60567 =
                   let uu____60580 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60580 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60567 with
                  | (t_x,uu____60593,guard) ->
                      let x1 =
                        let uu___620_60608 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60608.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60608.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60609 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60609)))
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
                | uu____60681 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60689) ->
              let uu____60694 = FStar_Syntax_Util.type_u ()  in
              (match uu____60694 with
               | (k,uu____60720) ->
                   let uu____60721 =
                     let uu____60734 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60734 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60721 with
                    | (t,uu____60761,g) ->
                        let x1 =
                          let uu___646_60776 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60776.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60776.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60777 =
                          let uu____60790 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60790 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60777 with
                         | (e,uu____60817,g') ->
                             let p2 =
                               let uu___653_60834 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60834.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60837 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60837, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60845 = intro_bv env1 x  in
              (match uu____60845 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60885 = intro_bv env1 x  in
              (match uu____60885 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60944 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____61083  ->
                        fun uu____61084  ->
                          match (uu____61083, uu____61084) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61293 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61293 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61372 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61372, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60944 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61510 =
                       let uu____61515 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61516 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61515 uu____61516
                        in
                     uu____61510 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61521 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61532 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61543 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61521, uu____61532, uu____61543, env2, e, guard,
                     (let uu___704_61561 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61561.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61606 = pat_as_arg_with_env env1 p2  in
          match uu____61606 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61664 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61664 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61698 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61698)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61720 -> (b, a, w, arg, guard, p3))
           in
        let uu____61729 = one_pat env p  in
        match uu____61729 with
        | (b,uu____61759,uu____61760,tm,guard,p1) -> (b, tm, guard, p1)
  