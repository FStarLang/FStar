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
              (fun uu____59814  ->
                 match uu____59814 with
                 | (p1,imp) ->
                     let uu____59829 = elaborate_pat env p1  in
                     (uu____59829, imp)) pats
             in
          let uu____59831 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59831 with
           | (uu____59836,t) ->
               let uu____59838 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59838 with
                | (f,uu____59854) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59992::uu____59993) ->
                          let uu____60040 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____60040
                      | (uu____60052::uu____60053,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60135  ->
                                  match uu____60135 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60165 =
                                               let uu____60168 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60168
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60165
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60170 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60170, true)
                                       | uu____60177 ->
                                           let uu____60180 =
                                             let uu____60186 =
                                               let uu____60188 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60188
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60186)
                                              in
                                           let uu____60192 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60180 uu____60192)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60273,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60287 ->
                                    let uu____60294 = aux formals' pats'  in
                                    (p1, true) :: uu____60294
                                | FStar_Syntax_Syntax.Pat_wild uu____60315 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60320 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60320
                                       in
                                    let uu____60321 = aux formals' pats'  in
                                    (p2, true) :: uu____60321
                                | uu____60342 ->
                                    let uu____60343 =
                                      let uu____60349 =
                                        let uu____60351 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60351
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60349)
                                       in
                                    FStar_Errors.raise_error uu____60343
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60364,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60365))
                               when p_imp ->
                               let uu____60369 = aux formals' pats'  in
                               (p1, true) :: uu____60369
                           | (uu____60390,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60399 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60399  in
                               let uu____60400 = aux formals' pats2  in
                               (p2, true) :: uu____60400
                           | (uu____60421,imp) ->
                               let uu____60427 =
                                 let uu____60435 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60435)  in
                               let uu____60440 = aux formals' pats'  in
                               uu____60427 :: uu____60440)
                       in
                    let uu___598_60457 = p  in
                    let uu____60458 =
                      let uu____60459 =
                        let uu____60473 = aux f pats1  in (fv, uu____60473)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60459  in
                    {
                      FStar_Syntax_Syntax.v = uu____60458;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60457.FStar_Syntax_Syntax.p)
                    }))
      | uu____60492 -> p
  
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
            ((let uu___611_60556 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60556.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60556.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60559 = FStar_Syntax_Util.type_u ()  in
             match uu____60559 with
             | (t,uu____60571) ->
                 let uu____60572 =
                   let uu____60585 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60585 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60572 with
                  | (t_x,uu____60598,guard) ->
                      let x1 =
                        let uu___620_60613 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60613.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60613.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60614 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60614)))
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
                | uu____60686 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60694) ->
              let uu____60699 = FStar_Syntax_Util.type_u ()  in
              (match uu____60699 with
               | (k,uu____60725) ->
                   let uu____60726 =
                     let uu____60739 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60739 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60726 with
                    | (t,uu____60766,g) ->
                        let x1 =
                          let uu___646_60781 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60781.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60781.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60782 =
                          let uu____60795 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60795 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60782 with
                         | (e,uu____60822,g') ->
                             let p2 =
                               let uu___653_60839 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60839.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60842 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60842, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60850 = intro_bv env1 x  in
              (match uu____60850 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60890 = intro_bv env1 x  in
              (match uu____60890 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60949 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____61088  ->
                        fun uu____61089  ->
                          match (uu____61088, uu____61089) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61298 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61298 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61377 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61377, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60949 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61515 =
                       let uu____61520 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61521 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61520 uu____61521
                        in
                     uu____61515 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61526 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61537 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61548 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61526, uu____61537, uu____61548, env2, e, guard,
                     (let uu___704_61566 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61566.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61611 = pat_as_arg_with_env env1 p2  in
          match uu____61611 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61669 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61669 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61703 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61703)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61725 -> (b, a, w, arg, guard, p3))
           in
        let uu____61734 = one_pat env p  in
        match uu____61734 with
        | (b,uu____61764,uu____61765,tm,guard,p1) -> (b, tm, guard, p1)
  