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
              (fun uu____59712  ->
                 match uu____59712 with
                 | (p1,imp) ->
                     let uu____59727 = elaborate_pat env p1  in
                     (uu____59727, imp)) pats
             in
          let uu____59729 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59729 with
           | (uu____59734,t) ->
               let uu____59736 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59736 with
                | (f,uu____59752) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59890::uu____59891) ->
                          let uu____59938 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____59938
                      | (uu____59950::uu____59951,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60033  ->
                                  match uu____60033 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60063 =
                                               let uu____60066 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60066
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60063
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60068 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60068, true)
                                       | uu____60075 ->
                                           let uu____60078 =
                                             let uu____60084 =
                                               let uu____60086 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60086
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60084)
                                              in
                                           let uu____60090 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60078 uu____60090)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60171,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60185 ->
                                    let uu____60192 = aux formals' pats'  in
                                    (p1, true) :: uu____60192
                                | FStar_Syntax_Syntax.Pat_wild uu____60213 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60218 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60218
                                       in
                                    let uu____60219 = aux formals' pats'  in
                                    (p2, true) :: uu____60219
                                | uu____60240 ->
                                    let uu____60241 =
                                      let uu____60247 =
                                        let uu____60249 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60249
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60247)
                                       in
                                    FStar_Errors.raise_error uu____60241
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60262,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60263))
                               when p_imp ->
                               let uu____60267 = aux formals' pats'  in
                               (p1, true) :: uu____60267
                           | (uu____60288,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60297 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60297  in
                               let uu____60298 = aux formals' pats2  in
                               (p2, true) :: uu____60298
                           | (uu____60319,imp) ->
                               let uu____60325 =
                                 let uu____60333 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60333)  in
                               let uu____60338 = aux formals' pats'  in
                               uu____60325 :: uu____60338)
                       in
                    let uu___598_60355 = p  in
                    let uu____60356 =
                      let uu____60357 =
                        let uu____60371 = aux f pats1  in (fv, uu____60371)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60357  in
                    {
                      FStar_Syntax_Syntax.v = uu____60356;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60355.FStar_Syntax_Syntax.p)
                    }))
      | uu____60390 -> p
  
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
            ((let uu___611_60454 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60454.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60454.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60457 = FStar_Syntax_Util.type_u ()  in
             match uu____60457 with
             | (t,uu____60469) ->
                 let uu____60470 =
                   let uu____60483 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60483 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60470 with
                  | (t_x,uu____60496,guard) ->
                      let x1 =
                        let uu___620_60511 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60511.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60511.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60512 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60512)))
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
                | uu____60584 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60592) ->
              let uu____60597 = FStar_Syntax_Util.type_u ()  in
              (match uu____60597 with
               | (k,uu____60623) ->
                   let uu____60624 =
                     let uu____60637 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60637 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60624 with
                    | (t,uu____60664,g) ->
                        let x1 =
                          let uu___646_60679 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60679.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60679.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60680 =
                          let uu____60693 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60693 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60680 with
                         | (e,uu____60720,g') ->
                             let p2 =
                               let uu___653_60737 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60737.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60740 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60740, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60748 = intro_bv env1 x  in
              (match uu____60748 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60788 = intro_bv env1 x  in
              (match uu____60788 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60847 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____60986  ->
                        fun uu____60987  ->
                          match (uu____60986, uu____60987) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61196 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61196 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61275 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61275, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60847 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61413 =
                       let uu____61418 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61419 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61418 uu____61419
                        in
                     uu____61413 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61424 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61435 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61446 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61424, uu____61435, uu____61446, env2, e, guard,
                     (let uu___704_61464 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61464.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61509 = pat_as_arg_with_env env1 p2  in
          match uu____61509 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61567 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61567 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61601 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61601)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61623 -> (b, a, w, arg, guard, p3))
           in
        let uu____61632 = one_pat env p  in
        match uu____61632 with
        | (b,uu____61662,uu____61663,tm,guard,p1) -> (b, tm, guard, p1)
  