open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option,FStar_Syntax_Syntax.lcomp)
    FStar_Pervasives_Native.tuple2
let (pat_as_exp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat ->
      (FStar_Syntax_Syntax.bv Prims.list,FStar_Syntax_Syntax.term,FStar_TypeChecker_Env.guard_t,
        FStar_Syntax_Syntax.pat) FStar_Pervasives_Native.tuple4)
  =
  fun env  ->
    fun p  ->
      let check_bv env1 x =
        let uu____56 = FStar_Syntax_Util.type_u ()  in
        match uu____56 with
        | (t,uu____66) ->
            let uu____67 =
              let uu____80 = FStar_Syntax_Syntax.range_of_bv x  in
              FStar_TypeChecker_Env.new_implicit_var_aux "pattern bv type"
                uu____80 env1 t FStar_Syntax_Syntax.Allow_untyped
               in
            (match uu____67 with
             | (t_x,uu____86,guard) ->
                 ((let uu___251_101 = x  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___251_101.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___251_101.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = t_x
                   }), guard))
         in
      let rec pat_as_arg_with_env env1 p1 =
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_constant c ->
            let e =
              match c with
              | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw)
                  ->
                  FStar_ToSyntax_ToSyntax.desugar_machine_integer
                    env1.FStar_TypeChecker_Env.dsenv repr sw
                    p1.FStar_Syntax_Syntax.p
              | uu____171 ->
                  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
                    FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
               in
            ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
        | FStar_Syntax_Syntax.Pat_dot_term (x,uu____179) ->
            let uu____184 = FStar_Syntax_Util.type_u ()  in
            (match uu____184 with
             | (k,uu____210) ->
                 let uu____211 =
                   let uu____224 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pat_dot_term type" uu____224 env1 k
                     FStar_Syntax_Syntax.Allow_untyped
                    in
                 (match uu____211 with
                  | (t,uu____246,g) ->
                      let x1 =
                        let uu___252_261 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___252_261.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___252_261.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t
                        }  in
                      let uu____262 =
                        let uu____275 = FStar_Syntax_Syntax.range_of_bv x1
                           in
                        FStar_TypeChecker_Env.new_implicit_var_aux
                          "pat_dot_term" uu____275 env1 t
                          FStar_Syntax_Syntax.Allow_untyped
                         in
                      (match uu____262 with
                       | (e,uu____297,g') ->
                           let p2 =
                             let uu___253_314 = p1  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                               FStar_Syntax_Syntax.p =
                                 (uu___253_314.FStar_Syntax_Syntax.p)
                             }  in
                           let uu____317 =
                             FStar_TypeChecker_Env.conj_guard g g'  in
                           ([], [], [], env1, e, uu____317, p2))))
        | FStar_Syntax_Syntax.Pat_wild x ->
            let uu____325 = check_bv env1 x  in
            (match uu____325 with
             | (x1,g) ->
                 let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                 let e =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                     FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                    in
                 ([x1], [], [x1], env2, e, g, p1))
        | FStar_Syntax_Syntax.Pat_var x ->
            let uu____363 = check_bv env1 x  in
            (match uu____363 with
             | (x1,g) ->
                 let env2 = FStar_TypeChecker_Env.push_bv env1 x1  in
                 let e =
                   FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                     FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                    in
                 ([x1], [x1], [], env2, e, g, p1))
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let uu____418 =
              FStar_All.pipe_right pats
                (FStar_List.fold_left
                   (fun uu____552  ->
                      fun uu____553  ->
                        match (uu____552, uu____553) with
                        | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                            let uu____751 = pat_as_arg_with_env env2 p2  in
                            (match uu____751 with
                             | (b',a',w',env3,te,guard',pat) ->
                                 let arg =
                                   if imp
                                   then FStar_Syntax_Syntax.iarg te
                                   else FStar_Syntax_Syntax.as_arg te  in
                                 let uu____827 =
                                   FStar_TypeChecker_Env.conj_guard guard
                                     guard'
                                    in
                                 ((b' :: b), (a' :: a), (w' :: w), env3, (arg
                                   :: args), uu____827, ((pat, imp) ::
                                   pats1))))
                   ([], [], [], env1, [],
                     FStar_TypeChecker_Env.trivial_guard, []))
               in
            (match uu____418 with
             | (b,a,w,env2,args,guard,pats1) ->
                 let e =
                   let uu____958 =
                     let uu____963 = FStar_Syntax_Syntax.fv_to_tm fv  in
                     let uu____964 = FStar_All.pipe_right args FStar_List.rev
                        in
                     FStar_Syntax_Syntax.mk_Tm_app uu____963 uu____964  in
                   uu____958 FStar_Pervasives_Native.None
                     p1.FStar_Syntax_Syntax.p
                    in
                 let uu____969 =
                   FStar_All.pipe_right (FStar_List.rev b) FStar_List.flatten
                    in
                 let uu____980 =
                   FStar_All.pipe_right (FStar_List.rev a) FStar_List.flatten
                    in
                 let uu____991 =
                   FStar_All.pipe_right (FStar_List.rev w) FStar_List.flatten
                    in
                 (uu____969, uu____980, uu____991, env2, e, guard,
                   (let uu___254_1009 = p1  in
                    {
                      FStar_Syntax_Syntax.v =
                        (FStar_Syntax_Syntax.Pat_cons
                           (fv, (FStar_List.rev pats1)));
                      FStar_Syntax_Syntax.p =
                        (uu___254_1009.FStar_Syntax_Syntax.p)
                    })))
         in
      let rec elaborate_pat env1 p1 =
        let maybe_dot inaccessible a r =
          if inaccessible
          then
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_dot_term (a, FStar_Syntax_Syntax.tun))
              r
          else FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a) r
           in
        match p1.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
            let pats1 =
              FStar_List.map
                (fun uu____1107  ->
                   match uu____1107 with
                   | (p2,imp) ->
                       let uu____1126 = elaborate_pat env1 p2  in
                       (uu____1126, imp)) pats
               in
            let uu____1131 =
              FStar_TypeChecker_Env.lookup_datacon env1
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            (match uu____1131 with
             | (uu____1138,t) ->
                 let uu____1140 = FStar_Syntax_Util.arrow_formals t  in
                 (match uu____1140 with
                  | (f,uu____1158) ->
                      let rec aux formals pats2 =
                        match (formals, pats2) with
                        | ([],[]) -> []
                        | ([],uu____1288::uu____1289) ->
                            let uu____1332 =
                              FStar_Ident.range_of_lid
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_TooManyPatternArguments,
                                "Too many pattern arguments") uu____1332
                        | (uu____1341::uu____1342,[]) ->
                            FStar_All.pipe_right formals
                              (FStar_List.map
                                 (fun uu____1420  ->
                                    match uu____1420 with
                                    | (t1,imp) ->
                                        (match imp with
                                         | FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             inaccessible) ->
                                             let a =
                                               let uu____1447 =
                                                 let uu____1450 =
                                                   FStar_Syntax_Syntax.range_of_bv
                                                     t1
                                                    in
                                                 FStar_Pervasives_Native.Some
                                                   uu____1450
                                                  in
                                               FStar_Syntax_Syntax.new_bv
                                                 uu____1447
                                                 FStar_Syntax_Syntax.tun
                                                in
                                             let r =
                                               FStar_Ident.range_of_lid
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                in
                                             let uu____1452 =
                                               maybe_dot inaccessible a r  in
                                             (uu____1452, true)
                                         | uu____1457 ->
                                             let uu____1460 =
                                               let uu____1465 =
                                                 let uu____1466 =
                                                   FStar_Syntax_Print.pat_to_string
                                                     p1
                                                    in
                                                 FStar_Util.format1
                                                   "Insufficient pattern arguments (%s)"
                                                   uu____1466
                                                  in
                                               (FStar_Errors.Fatal_InsufficientPatternArguments,
                                                 uu____1465)
                                                in
                                             let uu____1467 =
                                               FStar_Ident.range_of_lid
                                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                                in
                                             FStar_Errors.raise_error
                                               uu____1460 uu____1467)))
                        | (f1::formals',(p2,p_imp)::pats') ->
                            (match f1 with
                             | (uu____1541,FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Implicit uu____1542))
                                 when p_imp ->
                                 let uu____1545 = aux formals' pats'  in
                                 (p2, true) :: uu____1545
                             | (uu____1562,FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Implicit inaccessible))
                                 ->
                                 let a =
                                   FStar_Syntax_Syntax.new_bv
                                     (FStar_Pervasives_Native.Some
                                        (p2.FStar_Syntax_Syntax.p))
                                     FStar_Syntax_Syntax.tun
                                    in
                                 let p3 =
                                   let uu____1570 =
                                     FStar_Ident.range_of_lid
                                       (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                      in
                                   maybe_dot inaccessible a uu____1570  in
                                 let uu____1571 = aux formals' pats2  in
                                 (p3, true) :: uu____1571
                             | (uu____1588,imp) ->
                                 let uu____1594 =
                                   let uu____1601 =
                                     FStar_Syntax_Syntax.is_implicit imp  in
                                   (p2, uu____1601)  in
                                 let uu____1604 = aux formals' pats'  in
                                 uu____1594 :: uu____1604)
                         in
                      let uu___255_1619 = p1  in
                      let uu____1622 =
                        let uu____1623 =
                          let uu____1636 = aux f pats1  in (fv, uu____1636)
                           in
                        FStar_Syntax_Syntax.Pat_cons uu____1623  in
                      {
                        FStar_Syntax_Syntax.v = uu____1622;
                        FStar_Syntax_Syntax.p =
                          (uu___255_1619.FStar_Syntax_Syntax.p)
                      }))
        | uu____1653 -> p1  in
      let one_pat env1 p1 =
        let p2 = elaborate_pat env1 p1  in
        let uu____1690 = pat_as_arg_with_env env1 p2  in
        match uu____1690 with
        | (b,a,w,env2,arg,guard,p3) ->
            let uu____1748 =
              FStar_All.pipe_right b
                (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
               in
            (match uu____1748 with
             | FStar_Pervasives_Native.Some x ->
                 let m = FStar_Syntax_Print.bv_to_string x  in
                 let err =
                   let uu____1780 =
                     FStar_Util.format1
                       "The pattern variable \"%s\" was used more than once"
                       m
                      in
                   (FStar_Errors.Fatal_NonLinearPatternVars, uu____1780)  in
                 FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
             | uu____1799 -> (b, a, w, arg, guard, p3))
         in
      let uu____1808 = one_pat env p  in
      match uu____1808 with
      | (b,uu____1838,uu____1839,tm,guard,p1) -> (b, tm, guard, p1)
  