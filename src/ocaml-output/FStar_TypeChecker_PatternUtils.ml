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
              (fun uu____55156  ->
                 match uu____55156 with
                 | (p1,imp) ->
                     let uu____55171 = elaborate_pat env p1  in
                     (uu____55171, imp)) pats
             in
          let uu____55173 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____55173 with
           | (uu____55178,t) ->
               let uu____55180 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____55180 with
                | (f,uu____55196) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____55334::uu____55335) ->
                          let uu____55382 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____55382
                      | (uu____55394::uu____55395,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____55477  ->
                                  match uu____55477 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____55507 =
                                               let uu____55510 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____55510
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____55507
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____55512 =
                                             maybe_dot inaccessible a r  in
                                           (uu____55512, true)
                                       | uu____55519 ->
                                           let uu____55522 =
                                             let uu____55528 =
                                               let uu____55530 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____55530
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____55528)
                                              in
                                           let uu____55534 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____55522 uu____55534)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____55615,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____55629 ->
                                    let uu____55636 = aux formals' pats'  in
                                    (p1, true) :: uu____55636
                                | FStar_Syntax_Syntax.Pat_wild uu____55657 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____55662 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____55662
                                       in
                                    let uu____55663 = aux formals' pats'  in
                                    (p2, true) :: uu____55663
                                | uu____55684 ->
                                    let uu____55685 =
                                      let uu____55691 =
                                        let uu____55693 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____55693
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____55691)
                                       in
                                    FStar_Errors.raise_error uu____55685
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____55706,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____55707))
                               when p_imp ->
                               let uu____55711 = aux formals' pats'  in
                               (p1, true) :: uu____55711
                           | (uu____55732,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____55741 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____55741  in
                               let uu____55742 = aux formals' pats2  in
                               (p2, true) :: uu____55742
                           | (uu____55763,imp) ->
                               let uu____55769 =
                                 let uu____55777 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____55777)  in
                               let uu____55782 = aux formals' pats'  in
                               uu____55769 :: uu____55782)
                       in
                    let uu___598_55799 = p  in
                    let uu____55800 =
                      let uu____55801 =
                        let uu____55815 = aux f pats1  in (fv, uu____55815)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____55801  in
                    {
                      FStar_Syntax_Syntax.v = uu____55800;
                      FStar_Syntax_Syntax.p =
                        (uu___598_55799.FStar_Syntax_Syntax.p)
                    }))
      | uu____55834 -> p
  
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
            ((let uu___611_55898 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_55898.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_55898.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____55901 = FStar_Syntax_Util.type_u ()  in
             match uu____55901 with
             | (t,uu____55913) ->
                 let uu____55914 =
                   let uu____55927 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____55927 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____55914 with
                  | (t_x,uu____55940,guard) ->
                      let x1 =
                        let uu___620_55955 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_55955.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_55955.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____55956 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____55956)))
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
                | uu____56028 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____56036) ->
              let uu____56041 = FStar_Syntax_Util.type_u ()  in
              (match uu____56041 with
               | (k,uu____56067) ->
                   let uu____56068 =
                     let uu____56081 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____56081 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____56068 with
                    | (t,uu____56108,g) ->
                        let x1 =
                          let uu___646_56123 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_56123.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_56123.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____56124 =
                          let uu____56137 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____56137 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____56124 with
                         | (e,uu____56164,g') ->
                             let p2 =
                               let uu___653_56181 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_56181.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____56184 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____56184, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____56192 = intro_bv env1 x  in
              (match uu____56192 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____56232 = intro_bv env1 x  in
              (match uu____56232 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____56291 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____56430  ->
                        fun uu____56431  ->
                          match (uu____56430, uu____56431) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____56640 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____56640 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____56719 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____56719, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____56291 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____56857 =
                       let uu____56862 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____56863 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____56862 uu____56863
                        in
                     uu____56857 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____56866 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____56877 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____56888 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____56866, uu____56877, uu____56888, env2, e, guard,
                     (let uu___704_56906 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_56906.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____56951 = pat_as_arg_with_env env1 p2  in
          match uu____56951 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____57009 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____57009 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____57043 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____57043)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____57065 -> (b, a, w, arg, guard, p3))
           in
        let uu____57074 = one_pat env p  in
        match uu____57074 with
        | (b,uu____57104,uu____57105,tm,guard,p1) -> (b, tm, guard, p1)
  