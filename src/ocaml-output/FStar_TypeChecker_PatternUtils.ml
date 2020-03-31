open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
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
              (fun uu____85  ->
                 match uu____85 with
                 | (p1,imp) ->
                     let uu____100 = elaborate_pat env p1  in
                     (uu____100, imp)) pats
             in
          let uu____102 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____102 with
           | (uu____107,t) ->
               let uu____109 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____109 with
                | (f,uu____117) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____239::uu____240) ->
                          let uu____287 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____287
                      | (uu____299::uu____300,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____382  ->
                                  match uu____382 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____412 =
                                               let uu____415 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____415
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____412
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____417 =
                                             maybe_dot inaccessible a r  in
                                           (uu____417, true)
                                       | uu____424 ->
                                           let uu____427 =
                                             let uu____433 =
                                               let uu____435 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____435
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____433)
                                              in
                                           let uu____439 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error uu____427
                                             uu____439)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____520,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____534
                                    ->
                                    let uu____541 = aux formals' pats'  in
                                    (p1, true) :: uu____541
                                | FStar_Syntax_Syntax.Pat_wild uu____562 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____567 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____567  in
                                    let uu____568 = aux formals' pats'  in
                                    (p2, true) :: uu____568
                                | uu____589 ->
                                    let uu____590 =
                                      let uu____596 =
                                        let uu____598 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____598
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____596)
                                       in
                                    FStar_Errors.raise_error uu____590
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____611,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____612)) when
                               p_imp ->
                               let uu____616 = aux formals' pats'  in
                               (p1, true) :: uu____616
                           | (uu____637,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____646 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____646  in
                               let uu____647 = aux formals' pats2  in
                               (p2, true) :: uu____647
                           | (uu____668,imp) ->
                               let uu____674 =
                                 let uu____682 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____682)  in
                               let uu____687 = aux formals' pats'  in
                               uu____674 :: uu____687)
                       in
                    let uu___82_704 = p  in
                    let uu____705 =
                      let uu____706 =
                        let uu____720 = aux f pats1  in (fv, uu____720)  in
                      FStar_Syntax_Syntax.Pat_cons uu____706  in
                    {
                      FStar_Syntax_Syntax.v = uu____705;
                      FStar_Syntax_Syntax.p =
                        (uu___82_704.FStar_Syntax_Syntax.p)
                    }))
      | uu____739 -> p
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.pat))
  =
  fun introduce_bv_uvars  ->
    fun env  ->
      fun p  ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___95_803 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___95_803.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___95_803.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____806 = FStar_Syntax_Util.type_u ()  in
             match uu____806 with
             | (t,uu____818) ->
                 let uu____819 =
                   let uu____832 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____832 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____819 with
                  | (t_x,uu____841,guard) ->
                      let x1 =
                        let uu___104_856 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___104_856.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___104_856.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____857 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____857)))
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
                | uu____929 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Common.trivial_guard,
                p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____937) ->
              let uu____942 = FStar_Syntax_Util.type_u ()  in
              (match uu____942 with
               | (k,uu____968) ->
                   let uu____969 =
                     let uu____982 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____982 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____969 with
                    | (t,uu____1005,g) ->
                        let x1 =
                          let uu___130_1020 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___130_1020.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___130_1020.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____1021 =
                          let uu____1034 = FStar_Syntax_Syntax.range_of_bv x1
                             in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____1034 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____1021 with
                         | (e,uu____1057,g') ->
                             let p2 =
                               let uu___137_1074 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___137_1074.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____1077 =
                               FStar_TypeChecker_Common.conj_guard g g'  in
                             ([], [], [], env1, e, uu____1077, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1085 = intro_bv env1 x  in
              (match uu____1085 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1125 = intro_bv env1 x  in
              (match uu____1125 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1184 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1323  ->
                        fun uu____1324  ->
                          match (uu____1323, uu____1324) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____1533 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____1533 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____1612 =
                                     FStar_TypeChecker_Common.conj_guard
                                       guard guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1612, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Common.trivial_guard, []))
                 in
              (match uu____1184 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____1750 =
                       let uu____1755 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____1756 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____1755 uu____1756
                        in
                     uu____1750 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____1759 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1770 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1781 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1759, uu____1770, uu____1781, env2, e, guard,
                     (let uu___188_1799 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___188_1799.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1844 = pat_as_arg_with_env env1 p2  in
          match uu____1844 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____1902 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1902 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____1936 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1936)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1958 -> (b, a, w, arg, guard, p3))
           in
        let uu____1967 = one_pat env p  in
        match uu____1967 with
        | (b,uu____1997,uu____1998,tm,guard,p1) -> (b, tm, guard, p1)
  