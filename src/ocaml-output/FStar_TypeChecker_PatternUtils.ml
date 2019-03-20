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
              (fun uu____55157  ->
                 match uu____55157 with
                 | (p1,imp) ->
                     let uu____55172 = elaborate_pat env p1  in
                     (uu____55172, imp)) pats
             in
          let uu____55174 =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____55174 with
           | (uu____55179,t) ->
               let uu____55181 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____55181 with
                | (f,uu____55197) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([],[]) -> []
                      | ([],uu____55335::uu____55336) ->
                          let uu____55383 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu____55383
                      | (uu____55395::uu____55396,[]) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun uu____55478  ->
                                  match uu____55478 with
                                  | (t1,imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu____55508 =
                                               let uu____55511 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____55511
                                                in
                                             FStar_Syntax_Syntax.new_bv
                                               uu____55508
                                               FStar_Syntax_Syntax.tun
                                              in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let uu____55513 =
                                             maybe_dot inaccessible a r  in
                                           (uu____55513, true)
                                       | uu____55520 ->
                                           let uu____55523 =
                                             let uu____55529 =
                                               let uu____55531 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p
                                                  in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu____55531
                                                in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu____55529)
                                              in
                                           let uu____55535 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           FStar_Errors.raise_error
                                             uu____55523 uu____55535)))
                      | (f1::formals',(p1,p_imp)::pats') ->
                          (match f1 with
                           | (uu____55616,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term
                                    uu____55630 ->
                                    let uu____55637 = aux formals' pats'  in
                                    (p1, true) :: uu____55637
                                | FStar_Syntax_Syntax.Pat_wild uu____55658 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    let p2 =
                                      let uu____55663 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                         in
                                      maybe_dot inaccessible a uu____55663
                                       in
                                    let uu____55664 = aux formals' pats'  in
                                    (p2, true) :: uu____55664
                                | uu____55685 ->
                                    let uu____55686 =
                                      let uu____55692 =
                                        let uu____55694 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu____55694
                                         in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu____55692)
                                       in
                                    FStar_Errors.raise_error uu____55686
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu____55707,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu____55708))
                               when p_imp ->
                               let uu____55712 = aux formals' pats'  in
                               (p1, true) :: uu____55712
                           | (uu____55733,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun
                                  in
                               let p2 =
                                 let uu____55742 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 maybe_dot inaccessible a uu____55742  in
                               let uu____55743 = aux formals' pats2  in
                               (p2, true) :: uu____55743
                           | (uu____55764,imp) ->
                               let uu____55770 =
                                 let uu____55778 =
                                   FStar_Syntax_Syntax.is_implicit imp  in
                                 (p1, uu____55778)  in
                               let uu____55783 = aux formals' pats'  in
                               uu____55770 :: uu____55783)
                       in
                    let uu___598_55800 = p  in
                    let uu____55801 =
                      let uu____55802 =
                        let uu____55816 = aux f pats1  in (fv, uu____55816)
                         in
                      FStar_Syntax_Syntax.Pat_cons uu____55802  in
                    {
                      FStar_Syntax_Syntax.v = uu____55801;
                      FStar_Syntax_Syntax.p =
                        (uu___598_55800.FStar_Syntax_Syntax.p)
                    }))
      | uu____55835 -> p
  
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
            ((let uu___611_55899 = x  in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___611_55899.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___611_55899.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
              }), FStar_TypeChecker_Env.trivial_guard, env1)
          else
            (let uu____55902 = FStar_Syntax_Util.type_u ()  in
             match uu____55902 with
             | (t,uu____55914) ->
                 let uu____55915 =
                   let uu____55928 = FStar_Syntax_Syntax.range_of_bv x  in
                   FStar_TypeChecker_Env.new_implicit_var_aux
                     "pattern bv type" uu____55928 env1 t
                     FStar_Syntax_Syntax.Allow_untyped
                     FStar_Pervasives_Native.None
                    in
                 (match uu____55915 with
                  | (t_x,uu____55941,guard) ->
                      let x1 =
                        let uu___620_55956 = x  in
                        {
                          FStar_Syntax_Syntax.ppname =
                            (uu___620_55956.FStar_Syntax_Syntax.ppname);
                          FStar_Syntax_Syntax.index =
                            (uu___620_55956.FStar_Syntax_Syntax.index);
                          FStar_Syntax_Syntax.sort = t_x
                        }  in
                      let uu____55957 = FStar_TypeChecker_Env.push_bv env1 x1
                         in
                      (x1, guard, uu____55957)))
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
                | uu____56029 ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_constant c)
                      FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                 in
              ([], [], [], env1, e, FStar_TypeChecker_Env.trivial_guard, p1)
          | FStar_Syntax_Syntax.Pat_dot_term (x,uu____56037) ->
              let uu____56042 = FStar_Syntax_Util.type_u ()  in
              (match uu____56042 with
               | (k,uu____56068) ->
                   let uu____56069 =
                     let uu____56082 = FStar_Syntax_Syntax.range_of_bv x  in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pat_dot_term type" uu____56082 env1 k
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None
                      in
                   (match uu____56069 with
                    | (t,uu____56109,g) ->
                        let x1 =
                          let uu___646_56124 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___646_56124.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___646_56124.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t
                          }  in
                        let uu____56125 =
                          let uu____56138 =
                            FStar_Syntax_Syntax.range_of_bv x1  in
                          FStar_TypeChecker_Env.new_implicit_var_aux
                            "pat_dot_term" uu____56138 env1 t
                            FStar_Syntax_Syntax.Allow_untyped
                            FStar_Pervasives_Native.None
                           in
                        (match uu____56125 with
                         | (e,uu____56165,g') ->
                             let p2 =
                               let uu___653_56182 = p1  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, e));
                                 FStar_Syntax_Syntax.p =
                                   (uu___653_56182.FStar_Syntax_Syntax.p)
                               }  in
                             let uu____56185 =
                               FStar_TypeChecker_Env.conj_guard g g'  in
                             ([], [], [], env1, e, uu____56185, p2))))
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu____56193 = intro_bv env1 x  in
              (match uu____56193 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [], [x1], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu____56233 = intro_bv env1 x  in
              (match uu____56233 with
               | (x1,g,env2) ->
                   let e =
                     FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_name x1)
                       FStar_Pervasives_Native.None p1.FStar_Syntax_Syntax.p
                      in
                   ([x1], [x1], [], env2, e, g, p1))
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu____56292 =
                FStar_All.pipe_right pats
                  (FStar_List.fold_left
                     (fun uu____56431  ->
                        fun uu____56432  ->
                          match (uu____56431, uu____56432) with
                          | ((b,a,w,env2,args,guard,pats1),(p2,imp)) ->
                              let uu____56641 = pat_as_arg_with_env env2 p2
                                 in
                              (match uu____56641 with
                               | (b',a',w',env3,te,guard',pat) ->
                                   let arg =
                                     if imp
                                     then FStar_Syntax_Syntax.iarg te
                                     else FStar_Syntax_Syntax.as_arg te  in
                                   let uu____56720 =
                                     FStar_TypeChecker_Env.conj_guard guard
                                       guard'
                                      in
                                   ((b' :: b), (a' :: a), (w' :: w), env3,
                                     (arg :: args), uu____56720, ((pat, imp)
                                     :: pats1))))
                     ([], [], [], env1, [],
                       FStar_TypeChecker_Env.trivial_guard, []))
                 in
              (match uu____56292 with
               | (b,a,w,env2,args,guard,pats1) ->
                   let e =
                     let uu____56858 =
                       let uu____56863 = FStar_Syntax_Syntax.fv_to_tm fv  in
                       let uu____56864 =
                         FStar_All.pipe_right args FStar_List.rev  in
                       FStar_Syntax_Syntax.mk_Tm_app uu____56863 uu____56864
                        in
                     uu____56858 FStar_Pervasives_Native.None
                       p1.FStar_Syntax_Syntax.p
                      in
                   let uu____56867 =
                     FStar_All.pipe_right (FStar_List.rev b)
                       FStar_List.flatten
                      in
                   let uu____56878 =
                     FStar_All.pipe_right (FStar_List.rev a)
                       FStar_List.flatten
                      in
                   let uu____56889 =
                     FStar_All.pipe_right (FStar_List.rev w)
                       FStar_List.flatten
                      in
                   (uu____56867, uu____56878, uu____56889, env2, e, guard,
                     (let uu___704_56907 = p1  in
                      {
                        FStar_Syntax_Syntax.v =
                          (FStar_Syntax_Syntax.Pat_cons
                             (fv, (FStar_List.rev pats1)));
                        FStar_Syntax_Syntax.p =
                          (uu___704_56907.FStar_Syntax_Syntax.p)
                      })))
           in
        let one_pat env1 p1 =
          let p2 = elaborate_pat env1 p1  in
          let uu____56952 = pat_as_arg_with_env env1 p2  in
          match uu____56952 with
          | (b,a,w,env2,arg,guard,p3) ->
              let uu____57010 =
                FStar_All.pipe_right b
                  (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq)
                 in
              (match uu____57010 with
               | FStar_Pervasives_Native.Some x ->
                   let m = FStar_Syntax_Print.bv_to_string x  in
                   let err =
                     let uu____57044 =
                       FStar_Util.format1
                         "The pattern variable \"%s\" was used more than once"
                         m
                        in
                     (FStar_Errors.Fatal_NonLinearPatternVars, uu____57044)
                      in
                   FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
               | uu____57066 -> (b, a, w, arg, guard, p3))
           in
        let uu____57075 = one_pat env p  in
        match uu____57075 with
        | (b,uu____57105,uu____57106,tm,guard,p1) -> (b, tm, guard, p1)
  