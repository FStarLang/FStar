open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let (pat_as_exp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.pat ->
        (FStar_TypeChecker_Env.env ->
           FStar_Syntax_Syntax.term ->
             (FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t)
               FStar_Pervasives_Native.tuple2)
          ->
          (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,
            FStar_TypeChecker_Env.guard_t,FStar_Syntax_Syntax.pat)
            FStar_Pervasives_Native.tuple4)
  =
  fun allow_implicits  ->
    fun env  ->
      fun p  ->
        fun tc_annot  ->
          let check_bv env1 x =
            let uu____84 = FStar_Syntax_Util.type_u ()  in
            match uu____84 with
            | (t,uu____94) ->
                let uu____95 =
                  let uu____108 = FStar_Syntax_Syntax.range_of_bv x  in
                  FStar_TypeChecker_Env.new_implicit_var_aux
                    "pattern bv type" uu____108 env1 t
                    FStar_Syntax_Syntax.Allow_untyped
                   in
                (match uu____95 with
                 | (t_x,uu____114,guard) ->
                     ((let uu___251_129 = x  in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___251_129.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___251_129.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = t_x
                       }), guard))
             in
          let rec pat_as_arg_with_env allow_wc_dependence env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr,FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu____204 ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                   in
                ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x,uu____212) ->
                let uu____217 = FStar_Syntax_Util.type_u ()  in
                (match uu____217 with
                 | (k,uu____243) ->
                     let uu____244 =
                       let uu____257 = FStar_Syntax_Syntax.range_of_bv x  in
                       FStar_TypeChecker_Env.new_implicit_var_aux
                         "pat_dot_term type" uu____257 env1 k
                         FStar_Syntax_Syntax.Allow_untyped
                        in
                     (match uu____244 with
                      | (t,uu____279,g) ->
                          let x1 =
                            let uu___252_294 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___252_294.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___252_294.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            }  in
                          let uu____295 =
                            let uu____308 =
                              FStar_Syntax_Syntax.range_of_bv x1  in
                            FStar_TypeChecker_Env.new_implicit_var_aux
                              "pat_dot_term" uu____308 env1 t
                              FStar_Syntax_Syntax.Allow_untyped
                             in
                          (match uu____295 with
                           | (e,uu____330,g') ->
                               let p2 =
                                 let uu___253_347 = p1  in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___253_347.FStar_Syntax_Syntax.p)
                                 }  in
                               let uu____350 =
                                 FStar_TypeChecker_Env.conj_guard g g'  in
                               ([], [], [], env1, e, uu____350, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu____358 = check_bv env1 x  in
                (match uu____358 with
                 | (x1,g) ->
                     let env2 =
                       if allow_wc_dependence
                       then FStar_TypeChecker_Env.push_bv env1 x1
                       else env1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu____397 = check_bv env1 x  in
                (match uu____397 with
                 | (x1,g) ->
                     let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let uu____452 =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu____586  ->
                          fun uu____587  ->
                            match (uu____586, uu____587) with
                            | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                                let uu____785 =
                                  pat_as_arg_with_env allow_wc_dependence
                                    env2 p2
                                   in
                                (match uu____785 with
                                 | (b',a',w',env3,te,guard',pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te  in
                                     let uu____861 =
                                       FStar_TypeChecker_Env.conj_guard guard
                                         guard'
                                        in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu____861, ((pat, imp)
                                       :: pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Env.trivial_guard, []))
                   in
                (match uu____452 with
                 | (b,a,w,env2,args,guard,pats1) ->
                     let e =
                       let uu____992 =
                         let uu____997 = FStar_Syntax_Syntax.fv_to_tm fv  in
                         let uu____998 =
                           FStar_All.pipe_right args FStar_List.rev  in
                         FStar_Syntax_Syntax.mk_Tm_app uu____997 uu____998
                          in
                       uu____992 FStar_Pervasives_Native.None
                         p1.FStar_Syntax_Syntax.p
                        in
                     let uu____1019 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten
                        in
                     let uu____1030 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten
                        in
                     let uu____1041 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten
                        in
                     (uu____1019, uu____1030, uu____1041, env2, e, guard,
                       (let uu___254_1059 = p1  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___254_1059.FStar_Syntax_Syntax.p)
                        })))
             in
          let rec elaborate_pat env1 p1 =
            let maybe_dot inaccessible a r =
              if allow_implicits && inaccessible
              then
                FStar_Syntax_Syntax.withinfo
                  (FStar_Syntax_Syntax.Pat_dot_term
                     (a, FStar_Syntax_Syntax.tun)) r
              else
                FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a)
                  r
               in
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                let pats1 =
                  FStar_List.map
                    (fun uu____1157  ->
                       match uu____1157 with
                       | (p2,imp) ->
                           let uu____1176 = elaborate_pat env1 p2  in
                           (uu____1176, imp)) pats
                   in
                let uu____1181 =
                  FStar_TypeChecker_Env.lookup_datacon env1
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                   in
                (match uu____1181 with
                 | (uu____1188,t) ->
                     let uu____1190 = FStar_Syntax_Util.arrow_formals t  in
                     (match uu____1190 with
                      | (f,uu____1208) ->
                          let rec aux formals pats2 =
                            match (formals, pats2) with
                            | ([],[]) -> []
                            | ([],uu____1338::uu____1339) ->
                                let uu____1382 =
                                  FStar_Ident.range_of_lid
                                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_TooManyPatternArguments,
                                    "Too many pattern arguments") uu____1382
                            | (uu____1391::uu____1392,[]) ->
                                FStar_All.pipe_right formals
                                  (FStar_List.map
                                     (fun uu____1470  ->
                                        match uu____1470 with
                                        | (t1,imp) ->
                                            (match imp with
                                             | FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Syntax.Implicit
                                                 inaccessible) ->
                                                 let a =
                                                   let uu____1497 =
                                                     let uu____1500 =
                                                       FStar_Syntax_Syntax.range_of_bv
                                                         t1
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____1500
                                                      in
                                                   FStar_Syntax_Syntax.new_bv
                                                     uu____1497
                                                     FStar_Syntax_Syntax.tun
                                                    in
                                                 let r =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 let uu____1502 =
                                                   maybe_dot inaccessible a r
                                                    in
                                                 (uu____1502, true)
                                             | uu____1507 ->
                                                 let uu____1510 =
                                                   let uu____1515 =
                                                     let uu____1516 =
                                                       FStar_Syntax_Print.pat_to_string
                                                         p1
                                                        in
                                                     FStar_Util.format1
                                                       "Insufficient pattern arguments (%s)"
                                                       uu____1516
                                                      in
                                                   (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                     uu____1515)
                                                    in
                                                 let uu____1517 =
                                                   FStar_Ident.range_of_lid
                                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                    in
                                                 FStar_Errors.raise_error
                                                   uu____1510 uu____1517)))
                            | (f1::formals',(p2,p_imp)::pats') ->
                                (match f1 with
                                 | (uu____1591,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    uu____1592)) when p_imp ->
                                     let uu____1595 = aux formals' pats'  in
                                     (p2, true) :: uu____1595
                                 | (uu____1612,FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Implicit
                                    inaccessible)) ->
                                     let a =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p2.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     let p3 =
                                       let uu____1620 =
                                         FStar_Ident.range_of_lid
                                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          in
                                       maybe_dot inaccessible a uu____1620
                                        in
                                     let uu____1621 = aux formals' pats2  in
                                     (p3, true) :: uu____1621
                                 | (uu____1638,imp) ->
                                     let uu____1644 =
                                       let uu____1651 =
                                         FStar_Syntax_Syntax.is_implicit imp
                                          in
                                       (p2, uu____1651)  in
                                     let uu____1654 = aux formals' pats'  in
                                     uu____1644 :: uu____1654)
                             in
                          let uu___255_1669 = p1  in
                          let uu____1672 =
                            let uu____1673 =
                              let uu____1686 = aux f pats1  in
                              (fv, uu____1686)  in
                            FStar_Syntax_Syntax.Pat_cons uu____1673  in
                          {
                            FStar_Syntax_Syntax.v = uu____1672;
                            FStar_Syntax_Syntax.p =
                              (uu___255_1669.FStar_Syntax_Syntax.p)
                          }))
            | uu____1703 -> p1  in
          let one_pat allow_wc_dependence env1 p1 =
            let p2 = elaborate_pat env1 p1  in
            let uu____1745 = pat_as_arg_with_env allow_wc_dependence env1 p2
               in
            match uu____1745 with
            | (b,a,w,env2,arg,guard,p3) ->
                let uu____1803 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                   in
                (match uu____1803 with
                 | FStar_Pervasives_Native.Some x ->
                     let m = FStar_Syntax_Print.bv_to_string x  in
                     let err =
                       let uu____1835 =
                         FStar_Util.format1
                           "The pattern variable \"%s\" was used more than once"
                           m
                          in
                       (FStar_Errors.Fatal_NonLinearPatternVars, uu____1835)
                        in
                     FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
                 | uu____1854 -> (b, a, w, arg, guard, p3))
             in
          let uu____1863 = one_pat true env p  in
          match uu____1863 with
          | (b,uu____1893,uu____1894,tm,guard,p1) -> (b, tm, guard, p1)
  