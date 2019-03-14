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
              (fun uu____55124  ->
                 match uu____55124 with
                 | (p1,imp) ->
                     let uu____55139 = elaborate_pat env p1  in
                     (uu____55139, imp)) pats
             in
          let uu____55141 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____55141 with
           | (uu____55146,t) ->
               let uu____55148 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____55148 with
                | (f,uu____55164) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____55302::uu____55303) ->
                          let uu____55350 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____55350
                      | (uu____55362::uu____55363,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____55445  ->
                                  match uu____55445 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____55475 =
                                               let uu____55478 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____55478
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____55475
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____55480 =
                                             maybe_dot inaccessible a r  in
                                           (uu____55480, true)
                                       | uu____55487 ->
                                           let uu____55490 =
                                             let uu____55496 =
                                               let uu____55498 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____55498
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____55496)
                                              in
                                           let uu____55502 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____55490 uu____55502)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____55583,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____55597 ->
                                    let uu____55604 = aux formals' pats'  in
                                    (p1, true) :: uu____55604
                                | FStar_Syntax_Syntax.Pat_wild uu____55625 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____55630 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____55630
                                       in
                                    let uu____55631 = aux formals' pats'  in
                                    (p2, true) :: uu____55631
                                | uu____55652 ->
                                    let uu____55653 =
                                      let uu____55659 =
                                        let uu____55661 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____55661
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____55659)
                                       in
                                    FStar_Errors.raise_error uu____55653
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____55674,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____55675))
                               when p_imp ->
                               let uu____55679 = aux formals' pats'  in
                               (p1, true) :: uu____55679
                           | (uu____55700,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____55709 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____55709  in
                               let uu____55710 = aux formals' pats2  in
                               (p2, true) :: uu____55710
                           | (uu____55731,imp) ->
                               let uu____55737 =
                                 let uu____55745 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____55745)  in
                               let uu____55750 = aux formals' pats'  in
                               uu____55737 :: uu____55750)
                       in
                    let uu___598_55767 = p  in
                    let uu____55768 =
                      let uu____55769 =
                        let uu____55783 = aux f pats1  in (fv, uu____55783)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____55769  in
                    {
                      FStar_Syntax_Syntax.v = uu____55768;
                      FStar_Syntax_Syntax.p =
                        (uu___598_55767.FStar_Syntax_Syntax.p)
                    }))
      | uu____55802 -> p
  
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
            ((let uu___611_55866 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_55866.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_55866.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____55869 = FStar_Syntax_Util.type_u ()  in
             match uu____55869 with
             | (t,uu____55881) ->
                 let uu____55882 =
                   let uu____55895 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____55895 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____55882 with
                  | (t_x,uu____55908,guard) ->
                      let x1 =
                        let uu___620_55923 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_55923.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_55923.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____55924 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____55924)))
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
                | uu____55996 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____56004) ->
              let uu____56009 = FStar_Syntax_Util.type_u ()  in
              (match uu____56009 with
               | (k,uu____56035) ->
                   let uu____56036 =
                     let uu____56049 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____56049 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____56036 with
                    | (t,uu____56076,g) ->
                        let x1 =
                          let uu___646_56091 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_56091.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_56091.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____56092 =
                          let uu____56105 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____56105 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____56092 with
                         | (e,uu____56132,g') ->
                             let p2 =
                               let uu___653_56149 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_56149.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____56152 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____56152, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____56160 = intro_bv env1 x  in
              (match uu____56160 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____56200 = intro_bv env1 x  in
              (match uu____56200 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____56259 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____56398  ->
                        fun uu____56399  ->
                          match (uu____56398, uu____56399) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____56608 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____56608 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____56687 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____56687, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____56259 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____56825 =
                       let uu____56830 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____56831 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____56830 uu____56831
                        in
                     uu____56825 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____56834 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____56845 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____56856 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____56834, uu____56845, uu____56856, env2, e, guard,
                     (let uu___704_56874 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_56874.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____56919 = pat_as_arg_with_env env1 p2  in
          match uu____56919 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____56977 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____56977 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____57011 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____57011)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____57033 -> (b, a, w, arg, guard, p3))
           in
        let uu____57042 = one_pat env p  in
        match uu____57042 with
        | (b,uu____57072,uu____57073,tm,guard,p1) -> (b, tm, guard, p1)
  