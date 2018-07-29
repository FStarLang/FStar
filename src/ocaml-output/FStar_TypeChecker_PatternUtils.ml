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
              (fun uu____77  ->
                 match uu____77 with
                 | (p1,imp) ->
                     let uu____88 = elaborate_pat env p1  in (uu____88, imp))
              pats
             in
          let uu____89 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____89 with
           | (uu____94,t) ->
               let uu____104 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____104 with
                | (f,uu____120) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____250::uu____251) ->
                          let uu____294 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____294
                      | (uu____303::uu____304,[]) ->
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
                                             let uu____409 =
                                               let uu____412 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____412
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____409
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____414 =
                                             maybe_dot inaccessible a r  in
                                           (uu____414, true)
                                       | uu____419 ->
                                           let uu____422 =
                                             let uu____427 =
                                               let uu____428 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____428
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____427)
                                              in
                                           let uu____429 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error uu____422
                                             uu____429)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____503,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____504)) when
                               p_imp ->
                               let uu____507 = aux formals' pats'  in
                               (p1, true) :: uu____507
                           | (uu____524,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____532 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____532  in
                               let uu____533 = aux formals' pats2  in
                               (p2, true) :: uu____533
                           | (uu____550,imp) ->
                               let uu____556 =
                                 let uu____563 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____563)  in
                               let uu____566 = aux formals' pats'  in
                               uu____556 :: uu____566)
                       in
                    let uu___251_581 = p  in
                    let uu____582 =
                      let uu____583 =
                        let uu____596 = aux f pats1  in (fv, uu____596)  in
                      FStar_Syntax_Syntax.Pat_cons uu____583  in
                    {
                      FStar_Syntax_Syntax.v = uu____582;
                      FStar_Syntax_Syntax.p =
                        (uu___251_581.FStar_Syntax_Syntax.p)
                    }))
      | uu____613 -> p
  
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
            ((let uu___252_673 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___252_673.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___252_673.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____675 = FStar_Syntax_Util.type_u ()  in
             match uu____675 with
             | (t,uu____687) ->
                 let uu____692 =
                   let uu____705 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____705 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                    in
                 (match uu____692 with
                  | (t_x,uu____713,guard) ->
                      let x1 =
                        let uu___253_732 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___253_732.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___253_732.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____733 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____733)))
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
                | uu____803 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____811) ->
              let uu____816 = FStar_Syntax_Util.type_u ()  in
              (match uu____816 with
               | (k,uu____842) ->
                   let uu____847 =
                     let uu____860 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____860 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                      in
                   (match uu____847 with
                    | (t,uu____882,g) ->
                        let x1 =
                          let uu___254_901 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___254_901.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___254_901.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____902 =
                          let uu____915 = FStar_Syntax_Syntax.range_of_bv x1
                             in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____915 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                           in
                        (match uu____902 with
                         | (e,uu____937,g') ->
                             let p2 =
                               let uu___255_958 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___255_958.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____961 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____961, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____969 = intro_bv env1 x  in
              (match uu____969 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____1009 = intro_bv env1 x  in
              (match uu____1009 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____1066 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____1206  ->
                        fun uu____1207  ->
                          match (uu____1206, uu____1207) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____1417 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____1417 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____1503 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____1503, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____1066 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____1648 =
                       let uu____1653 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____1654 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____1653 uu____1654
                        in
                     uu____1648 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____1659 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____1670 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____1681 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____1659, uu____1670, uu____1681, env2, e, guard,
                     (let uu___256_1699 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___256_1699.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____1748 = pat_as_arg_with_env env1 p2  in
          match uu____1748 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____1818 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____1818 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____1854 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____1854)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____1877 -> (b, a, w, arg, guard, p3))
           in
        let uu____1890 = one_pat env p  in
        match uu____1890 with
        | (b,uu____1924,uu____1925,tm,guard,p1) -> (b, tm, guard, p1)
  