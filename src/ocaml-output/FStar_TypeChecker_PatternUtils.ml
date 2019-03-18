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
              (fun uu____55123  ->
                 match uu____55123 with
                 | (p1,imp) ->
                     let uu____55138 = elaborate_pat env p1  in
                     (uu____55138, imp)) pats
             in
          let uu____55140 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____55140 with
           | (uu____55145,t) ->
               let uu____55147 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____55147 with
                | (f,uu____55163) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____55301::uu____55302) ->
                          let uu____55349 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____55349
                      | (uu____55361::uu____55362,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____55444  ->
                                  match uu____55444 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____55474 =
                                               let uu____55477 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____55477
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____55474
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____55479 =
                                             maybe_dot inaccessible a r  in
                                           (uu____55479, true)
                                       | uu____55486 ->
                                           let uu____55489 =
                                             let uu____55495 =
                                               let uu____55497 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____55497
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____55495)
                                              in
                                           let uu____55501 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____55489 uu____55501)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____55582,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____55596 ->
                                    let uu____55603 = aux formals' pats'  in
                                    (p1, true) :: uu____55603
                                | FStar_Syntax_Syntax.Pat_wild uu____55624 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____55629 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____55629
                                       in
                                    let uu____55630 = aux formals' pats'  in
                                    (p2, true) :: uu____55630
                                | uu____55651 ->
                                    let uu____55652 =
                                      let uu____55658 =
                                        let uu____55660 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____55660
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____55658)
                                       in
                                    FStar_Errors.raise_error uu____55652
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____55673,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____55674))
                               when p_imp ->
                               let uu____55678 = aux formals' pats'  in
                               (p1, true) :: uu____55678
                           | (uu____55699,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____55708 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____55708  in
                               let uu____55709 = aux formals' pats2  in
                               (p2, true) :: uu____55709
                           | (uu____55730,imp) ->
                               let uu____55736 =
                                 let uu____55744 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____55744)  in
                               let uu____55749 = aux formals' pats'  in
                               uu____55736 :: uu____55749)
                       in
                    let uu___598_55766 = p  in
                    let uu____55767 =
                      let uu____55768 =
                        let uu____55782 = aux f pats1  in (fv, uu____55782)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____55768  in
                    {
                      FStar_Syntax_Syntax.v = uu____55767;
                      FStar_Syntax_Syntax.p =
                        (uu___598_55766.FStar_Syntax_Syntax.p)
                    }))
      | uu____55801 -> p
  
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
            ((let uu___611_55865 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_55865.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_55865.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____55868 = FStar_Syntax_Util.type_u ()  in
             match uu____55868 with
             | (t,uu____55880) ->
                 let uu____55881 =
                   let uu____55894 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____55894 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____55881 with
                  | (t_x,uu____55907,guard) ->
                      let x1 =
                        let uu___620_55922 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_55922.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_55922.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____55923 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____55923)))
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
                | uu____55995 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____56003) ->
              let uu____56008 = FStar_Syntax_Util.type_u ()  in
              (match uu____56008 with
               | (k,uu____56034) ->
                   let uu____56035 =
                     let uu____56048 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____56048 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____56035 with
                    | (t,uu____56075,g) ->
                        let x1 =
                          let uu___646_56090 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_56090.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_56090.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____56091 =
                          let uu____56104 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____56104 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____56091 with
                         | (e,uu____56131,g') ->
                             let p2 =
                               let uu___653_56148 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_56148.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____56151 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____56151, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____56159 = intro_bv env1 x  in
              (match uu____56159 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____56199 = intro_bv env1 x  in
              (match uu____56199 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____56258 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____56397  ->
                        fun uu____56398  ->
                          match (uu____56397, uu____56398) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____56607 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____56607 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____56686 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____56686, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____56258 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____56824 =
                       let uu____56829 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____56830 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____56829 uu____56830
                        in
                     uu____56824 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____56833 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____56844 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____56855 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____56833, uu____56844, uu____56855, env2, e, guard,
                     (let uu___704_56873 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_56873.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____56918 = pat_as_arg_with_env env1 p2  in
          match uu____56918 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____56976 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____56976 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____57010 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____57010)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____57032 -> (b, a, w, arg, guard, p3))
           in
        let uu____57041 = one_pat env p  in
        match uu____57041 with
        | (b,uu____57071,uu____57072,tm,guard,p1) -> (b, tm, guard, p1)
  