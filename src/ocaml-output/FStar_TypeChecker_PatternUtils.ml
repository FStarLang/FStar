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
              (fun uu____243  ->
                 match uu____243 with
                 | (p1,imp) ->
                     let uu____258 = elaborate_pat env p1  in
                     (uu____258, imp)) pats
             in
          let uu____260 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____260 with
           | (uu____273,t) ->
               let uu____283 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____283 with
                | (f,uu____308) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____510::uu____511) ->
                          let uu____580 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____580
                      | (uu____599::uu____600,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____724  ->
                                  match uu____724 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____785 =
                                               let uu____788 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____788
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____785
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____794 =
                                             maybe_dot inaccessible a r  in
                                           (uu____794, true)
                                       | uu____807 ->
                                           let uu____810 =
                                             let uu____816 =
                                               let uu____818 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____818
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____816)
                                              in
                                           let uu____822 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error uu____810
                                             uu____822)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____948,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____975
                                    ->
                                    let uu____991 = aux formals' pats'  in
                                    (p1, true) :: uu____991
                                | FStar_Syntax_Syntax.Pat_wild uu____1021 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____1044 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____1044  in
                                    let uu____1049 = aux formals' pats'  in
                                    (p2, true) :: uu____1049
                                | uu____1079 ->
                                    let uu____1080 =
                                      let uu____1086 =
                                        let uu____1088 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____1088
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____1086)
                                       in
                                    FStar_Errors.raise_error uu____1080
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____1104,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____1105)) when
                               p_imp ->
                               let uu____1119 = aux formals' pats'  in
                               (p1, true) :: uu____1119
                           | (uu____1149,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____1181 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____1181  in
                               let uu____1186 = aux formals' pats2  in
                               (p2, true) :: uu____1186
                           | (uu____1216,imp) ->
                               let uu____1232 =
                                 let uu____1243 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____1243)  in
                               let uu____1251 = aux formals' pats'  in
                               uu____1232 :: uu____1251)
                       in
                    let uu___82_1274 = p  in
                    let uu____1275 =
                      let uu____1276 =
                        let uu____1296 = aux f pats1  in (fv, uu____1296)  in
                      FStar_Syntax_Syntax.Pat_cons uu____1276  in
                    {
                      FStar_Syntax_Syntax.v = uu____1275;
                      FStar_Syntax_Syntax.p =
                        (uu___82_1274.FStar_Syntax_Syntax.p)
                    }))
      | uu____1324 -> p
  
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
            ((let uu___95_1829 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_1829.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_1829.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____1842 = FStar_Syntax_Util.type_u ()  in
             match uu____1842 with
             | (t,uu____1921) ->
                 let uu____1930 =
                   let uu____1959 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____1959 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____1930 with
                  | (t_x,uu____2039,guard) ->
                      let x1 =
                        let uu___104_2096 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___104_2096.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___104_2096.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____2107 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____2107)))
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
                | uu____2624 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____2724) ->
              let uu____2747 = FStar_Syntax_Util.type_u ()  in
              (match uu____2747 with
               | (k,uu____2854) ->
                   let uu____2863 =
                     let uu____2892 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____2892 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____2863 with
                    | (t,uu____3000,g) ->
                        let x1 =
                          let uu___130_3057 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_3057.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_3057.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____3068 =
                          let uu____3097 = FStar_Syntax_Syntax.range_of_bv x1
                             in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____3097 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____3068 with
                         | (e,uu____3205,g') ->
                             let p2 =
                               let uu___137_3257 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___137_3257.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____3269 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____3269, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____3382 = intro_bv env1 x  in
              (match uu____3382 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____3803 = intro_bv env1 x  in
              (match uu____3803 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____4250 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____4608  ->
                        fun uu____4609  ->
                          match (uu____4608, uu____4609) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____5256 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____5256 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____5639 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____5639, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____4250 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____6192 =
                       let uu____6197 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____6206 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____6197 uu____6206
                        in
                     uu____6192 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____6209 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____6245 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____6281 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____6209, uu____6245, uu____6281, env2, e, guard,
                     (let uu___188_6401 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___188_6401.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____6583 = pat_as_arg_with_env env1 p2  in
          match uu____6583 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____6895 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____6895 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____6982 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____6982)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____7027 -> (b, a, w, arg, guard, p3))
           in
        let uu____7064 = one_pat env p  in
        match uu____7064 with
        | (b,uu____7130,uu____7131,tm,guard,p1) -> (b, tm, guard, p1)
  