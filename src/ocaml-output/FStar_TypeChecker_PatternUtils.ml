open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
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
              (fun uu____86  ->
                 match uu____86 with
                 | (p1,imp) ->
                     let uu____101 = elaborate_pat env p1  in
                     (uu____101, imp)) pats
             in
          let uu____103 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____103 with
           | (uu____108,t) ->
               let uu____110 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____110 with
                | (f,uu____126) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____264::uu____265) ->
                          let uu____312 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____312
                      | (uu____324::uu____325,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____407  ->
                                  match uu____407 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____437 =
                                               let uu____440 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____440
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____437
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____442 =
                                             maybe_dot inaccessible a r  in
                                           (uu____442, true)
                                       | uu____449 ->
                                           let uu____452 =
                                             let uu____458 =
                                               let uu____460 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____460
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____458)
                                              in
                                           let uu____464 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error uu____452
                                             uu____464)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____545,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu____559
                                    ->
                                    let uu____566 = aux formals' pats'  in
                                    (p1, true) :: uu____566
                                | FStar_Syntax_Syntax.Pat_wild uu____587 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____592 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____592  in
                                    let uu____593 = aux formals' pats'  in
                                    (p2, true) :: uu____593
                                | uu____614 ->
                                    let uu____615 =
                                      let uu____621 =
                                        let uu____623 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____623
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____621)
                                       in
                                    FStar_Errors.raise_error uu____615
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____636,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____637)) when
                               p_imp ->
                               let uu____641 = aux formals' pats'  in
                               (p1, true) :: uu____641
                           | (uu____662,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____671 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____671  in
                               let uu____672 = aux formals' pats2  in
                               (p2, true) :: uu____672
                           | (uu____693,imp) ->
                               let uu____699 =
                                 let uu____707 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____707)  in
                               let uu____712 = aux formals' pats'  in
                               uu____699 :: uu____712)
                       in
                    let uu___265_729 = p  in
                    let uu____730 =
                      let uu____731 =
                        let uu____745 = aux f pats1  in (fv, uu____745)  in
                      FStar_Syntax_Syntax.Pat_cons uu____731  in
                    {
                      FStar_Syntax_Syntax.v = uu____730;
                      FStar_Syntax_Syntax.p =
                        (uu___265_729.FStar_Syntax_Syntax.p)
                    }))
      | uu____764 -> p
  
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,
          FStar_Syntax_Syntax.pat) FStar_Pervasives_Native.tuple4)
  =
  fun introduce_bv_uvars  ->
    fun env  ->
      fun p  ->
        let intro_bv env1 x =
          if Prims.op_Negation introduce_bv_uvars
          then
            ((let uu___266_828 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___266_828.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___266_828.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____831 = FStar_Syntax_Util.type_u ()  in
             match uu____831 with
             | (t,uu____843) ->
                 let uu____844 =
                   let uu____857 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____857 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                    in
                 (match uu____844 with
                  | (t_x,uu____866,guard) ->
                      let x1 =
                        let uu___267_881 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___267_881.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___267_881.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____882 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____882)))
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
                | uu____954 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____962) ->
              let uu____967 = FStar_Syntax_Util.type_u ()  in
              (match uu____967 with
               | (k,uu____993) ->
                   let uu____994 =
                     let uu____1007 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____1007 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                      in
                   (match uu____994 with
                    | (t,uu____1030,g) ->
                        let x1 =
                          let uu___268_1045 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___268_1045.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___268_1045.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____1046 =
                          let uu____1059 = FStar_Syntax_Syntax.range_of_bv x1
                             in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____1059 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                           in
                        (match uu____1046 with
                         | (e,uu____1082,g') ->
                             let p2 =
                               let uu___269_1099 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___269_1099.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____1102 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____1102, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____1110 = intro_bv env1 x  in
              (match uu____1110 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1150 = intro_bv env1 x  in
              (match uu____1150 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1209 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1348  ->
                        fun uu____1349  ->
                          match (uu____1348, uu____1349) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____1558 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____1558 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____1637 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1637, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____1209 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____1775 =
                       let uu____1780 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____1781 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____1780 uu____1781
                        in
                     uu____1775 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____1786 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1797 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1808 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1786, uu____1797, uu____1808, env2, e, guard,
                     (let uu___270_1826 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___270_1826.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1871 = pat_as_arg_with_env env1 p2  in
          match uu____1871 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____1929 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1929 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____1963 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1963)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1985 -> (b, a, w, arg, guard, p3))
           in
        let uu____1994 = one_pat env p  in
        match uu____1994 with
        | (b,uu____2024,uu____2025,tm,guard,p1) -> (b, tm, guard, p1)
  