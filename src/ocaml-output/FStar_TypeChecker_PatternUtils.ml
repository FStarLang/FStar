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
              (fun uu____59717  ->
                 match uu____59717 with
                 | (p1,imp) ->
                     let uu____59732 = elaborate_pat env p1  in
                     (uu____59732, imp)) pats
             in
          let uu____59734 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____59734 with
           | (uu____59739,t) ->
               let uu____59741 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____59741 with
                | (f,uu____59757) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____59895::uu____59896) ->
                          let uu____59943 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____59943
                      | (uu____59955::uu____59956,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____60038  ->
                                  match uu____60038 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____60068 =
                                               let uu____60071 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____60071
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____60068
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____60073 =
                                             maybe_dot inaccessible a r  in
                                           (uu____60073, true)
                                       | uu____60080 ->
                                           let uu____60083 =
                                             let uu____60089 =
                                               let uu____60091 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____60091
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____60089)
                                              in
                                           let uu____60095 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____60083 uu____60095)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____60176,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____60190 ->
                                    let uu____60197 = aux formals' pats'  in
                                    (p1, true) :: uu____60197
                                | FStar_Syntax_Syntax.Pat_wild uu____60218 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____60223 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____60223
                                       in
                                    let uu____60224 = aux formals' pats'  in
                                    (p2, true) :: uu____60224
                                | uu____60245 ->
                                    let uu____60246 =
                                      let uu____60252 =
                                        let uu____60254 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____60254
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____60252)
                                       in
                                    FStar_Errors.raise_error uu____60246
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____60267,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____60268))
                               when p_imp ->
                               let uu____60272 = aux formals' pats'  in
                               (p1, true) :: uu____60272
                           | (uu____60293,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____60302 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____60302  in
                               let uu____60303 = aux formals' pats2  in
                               (p2, true) :: uu____60303
                           | (uu____60324,imp) ->
                               let uu____60330 =
                                 let uu____60338 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____60338)  in
                               let uu____60343 = aux formals' pats'  in
                               uu____60330 :: uu____60343)
                       in
                    let uu___598_60360 = p  in
                    let uu____60361 =
                      let uu____60362 =
                        let uu____60376 = aux f pats1  in (fv, uu____60376)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____60362  in
                    {
                      FStar_Syntax_Syntax.v = uu____60361;
                      FStar_Syntax_Syntax.p =
                        (uu___598_60360.FStar_Syntax_Syntax.p)
                    }))
      | uu____60395 -> p
  
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
            ((let uu___611_60459 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_60459.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_60459.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____60462 = FStar_Syntax_Util.type_u ()  in
             match uu____60462 with
             | (t,uu____60474) ->
                 let uu____60475 =
                   let uu____60488 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____60488 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____60475 with
                  | (t_x,uu____60501,guard) ->
                      let x1 =
                        let uu___620_60516 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_60516.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_60516.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____60517 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____60517)))
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
                | uu____60589 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____60597) ->
              let uu____60602 = FStar_Syntax_Util.type_u ()  in
              (match uu____60602 with
               | (k,uu____60628) ->
                   let uu____60629 =
                     let uu____60642 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____60642 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____60629 with
                    | (t,uu____60669,g) ->
                        let x1 =
                          let uu___646_60684 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_60684.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_60684.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____60685 =
                          let uu____60698 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____60698 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____60685 with
                         | (e,uu____60725,g') ->
                             let p2 =
                               let uu___653_60742 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_60742.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____60745 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____60745, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____60753 = intro_bv env1 x  in
              (match uu____60753 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____60793 = intro_bv env1 x  in
              (match uu____60793 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____60852 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____60991  ->
                        fun uu____60992  ->
                          match (uu____60991, uu____60992) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____61201 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____61201 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____61280 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____61280, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____60852 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____61418 =
                       let uu____61423 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____61424 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____61423 uu____61424
                        in
                     uu____61418 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____61429 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____61440 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____61451 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____61429, uu____61440, uu____61451, env2, e, guard,
                     (let uu___704_61469 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_61469.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____61514 = pat_as_arg_with_env env1 p2  in
          match uu____61514 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____61572 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____61572 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____61606 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____61606)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____61628 -> (b, a, w, arg, guard, p3))
           in
        let uu____61637 = one_pat env p  in
        match uu____61637 with
        | (b,uu____61667,uu____61668,tm,guard,p1) -> (b, tm, guard, p1)
  