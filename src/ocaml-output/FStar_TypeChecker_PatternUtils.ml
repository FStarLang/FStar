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
              (fun uu____59786  ->
                 match uu____59786 with
                 | (p1,imp) ->
                     let uu____59801 = elaborate_pat env p1  in
                     (uu____59801, imp)) pats
             in
          let uu____59803 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59803 with
           | (uu____59808,t) ->
               let uu____59810 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59810 with
                | (f,uu____59826) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59964::uu____59965) ->
                          let uu____60012 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____60012
                      | (uu____60024::uu____60025,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60107  ->
                                  match uu____60107 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60137 =
                                               let uu____60140 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60140
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60137
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60142 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60142, true)
                                       | uu____60149 ->
                                           let uu____60152 =
                                             let uu____60158 =
                                               let uu____60160 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60160
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60158)
                                              in
                                           let uu____60164 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60152 uu____60164)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60245,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60259 ->
                                    let uu____60266 = aux formals' pats'  in
                                    (p1, true) :: uu____60266
                                | FStar_Syntax_Syntax.Pat_wild uu____60287 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60292 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60292
                                       in
                                    let uu____60293 = aux formals' pats'  in
                                    (p2, true) :: uu____60293
                                | uu____60314 ->
                                    let uu____60315 =
                                      let uu____60321 =
                                        let uu____60323 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60323
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60321)
                                       in
                                    FStar_Errors.raise_error uu____60315
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60336,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60337))
                               when p_imp ->
                               let uu____60341 = aux formals' pats'  in
                               (p1, true) :: uu____60341
                           | (uu____60362,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60371 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60371  in
                               let uu____60372 = aux formals' pats2  in
                               (p2, true) :: uu____60372
                           | (uu____60393,imp) ->
                               let uu____60399 =
                                 let uu____60407 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60407)  in
                               let uu____60412 = aux formals' pats'  in
                               uu____60399 :: uu____60412)
                       in
                    let uu___598_60429 = p  in
                    let uu____60430 =
                      let uu____60431 =
                        let uu____60445 = aux f pats1  in (fv, uu____60445)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60431  in
                    {
                      FStar_Syntax_Syntax.v = uu____60430;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60429.FStar_Syntax_Syntax.p)
                    }))
      | uu____60464 -> p
  
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
            ((let uu___611_60528 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60528.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60528.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60531 = FStar_Syntax_Util.type_u ()  in
             match uu____60531 with
             | (t,uu____60543) ->
                 let uu____60544 =
                   let uu____60557 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60557 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60544 with
                  | (t_x,uu____60570,guard) ->
                      let x1 =
                        let uu___620_60585 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60585.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60585.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60586 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60586)))
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
                | uu____60658 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60666) ->
              let uu____60671 = FStar_Syntax_Util.type_u ()  in
              (match uu____60671 with
               | (k,uu____60697) ->
                   let uu____60698 =
                     let uu____60711 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60711 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60698 with
                    | (t,uu____60738,g) ->
                        let x1 =
                          let uu___646_60753 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60753.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60753.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60754 =
                          let uu____60767 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60767 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60754 with
                         | (e,uu____60794,g') ->
                             let p2 =
                               let uu___653_60811 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60811.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60814 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60814, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60822 = intro_bv env1 x  in
              (match uu____60822 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60862 = intro_bv env1 x  in
              (match uu____60862 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60921 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____61060  ->
                        fun uu____61061  ->
                          match (uu____61060, uu____61061) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61270 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61270 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61349 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61349, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60921 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61487 =
                       let uu____61492 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61493 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61492 uu____61493
                        in
                     uu____61487 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61498 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61509 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61520 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61498, uu____61509, uu____61520, env2, e, guard,
                     (let uu___704_61538 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61538.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61583 = pat_as_arg_with_env env1 p2  in
          match uu____61583 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61641 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61641 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61675 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61675)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61697 -> (b, a, w, arg, guard, p3))
           in
        let uu____61706 = one_pat env p  in
        match uu____61706 with
        | (b,uu____61736,uu____61737,tm,guard,p1) -> (b, tm, guard, p1)
  