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
              (fun uu____59781  ->
                 match uu____59781 with
                 | (p1,imp) ->
                     let uu____59796 = elaborate_pat env p1  in
                     (uu____59796, imp)) pats
             in
          let uu____59798 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59798 with
           | (uu____59803,t) ->
               let uu____59805 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59805 with
                | (f,uu____59821) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59959::uu____59960) ->
                          let uu____60007 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____60007
                      | (uu____60019::uu____60020,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60102  ->
                                  match uu____60102 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60132 =
                                               let uu____60135 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60135
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60132
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60137 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60137, true)
                                       | uu____60144 ->
                                           let uu____60147 =
                                             let uu____60153 =
                                               let uu____60155 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60155
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60153)
                                              in
                                           let uu____60159 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60147 uu____60159)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60240,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60254 ->
                                    let uu____60261 = aux formals' pats'  in
                                    (p1, true) :: uu____60261
                                | FStar_Syntax_Syntax.Pat_wild uu____60282 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60287 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60287
                                       in
                                    let uu____60288 = aux formals' pats'  in
                                    (p2, true) :: uu____60288
                                | uu____60309 ->
                                    let uu____60310 =
                                      let uu____60316 =
                                        let uu____60318 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60318
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60316)
                                       in
                                    FStar_Errors.raise_error uu____60310
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60331,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60332))
                               when p_imp ->
                               let uu____60336 = aux formals' pats'  in
                               (p1, true) :: uu____60336
                           | (uu____60357,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60366 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60366  in
                               let uu____60367 = aux formals' pats2  in
                               (p2, true) :: uu____60367
                           | (uu____60388,imp) ->
                               let uu____60394 =
                                 let uu____60402 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60402)  in
                               let uu____60407 = aux formals' pats'  in
                               uu____60394 :: uu____60407)
                       in
                    let uu___598_60424 = p  in
                    let uu____60425 =
                      let uu____60426 =
                        let uu____60440 = aux f pats1  in (fv, uu____60440)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60426  in
                    {
                      FStar_Syntax_Syntax.v = uu____60425;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60424.FStar_Syntax_Syntax.p)
                    }))
      | uu____60459 -> p
  
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
            ((let uu___611_60523 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60523.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60523.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60526 = FStar_Syntax_Util.type_u ()  in
             match uu____60526 with
             | (t,uu____60538) ->
                 let uu____60539 =
                   let uu____60552 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60552 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60539 with
                  | (t_x,uu____60565,guard) ->
                      let x1 =
                        let uu___620_60580 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60580.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60580.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60581 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60581)))
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
                | uu____60653 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60661) ->
              let uu____60666 = FStar_Syntax_Util.type_u ()  in
              (match uu____60666 with
               | (k,uu____60692) ->
                   let uu____60693 =
                     let uu____60706 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60706 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60693 with
                    | (t,uu____60733,g) ->
                        let x1 =
                          let uu___646_60748 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60748.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60748.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60749 =
                          let uu____60762 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60762 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60749 with
                         | (e,uu____60789,g') ->
                             let p2 =
                               let uu___653_60806 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60806.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60809 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60809, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60817 = intro_bv env1 x  in
              (match uu____60817 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60857 = intro_bv env1 x  in
              (match uu____60857 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60916 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____61055  ->
                        fun uu____61056  ->
                          match (uu____61055, uu____61056) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61265 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61265 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61344 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61344, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60916 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61482 =
                       let uu____61487 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61488 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61487 uu____61488
                        in
                     uu____61482 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61493 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61504 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61515 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61493, uu____61504, uu____61515, env2, e, guard,
                     (let uu___704_61533 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61533.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61578 = pat_as_arg_with_env env1 p2  in
          match uu____61578 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61636 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61636 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61670 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61670)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61692 -> (b, a, w, arg, guard, p3))
           in
        let uu____61701 = one_pat env p  in
        match uu____61701 with
        | (b,uu____61731,uu____61732,tm,guard,p1) -> (b, tm, guard, p1)
  