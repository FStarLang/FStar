open Prims
type lcomp_with_binder =
  (FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStar_TypeChecker_Common.lcomp)
let rec (elaborate_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.pat -> FStar_Syntax_Syntax.pat)
  =
  fun env ->
    fun p ->
      let maybe_dot inaccessible a r =
        if inaccessible
        then
          FStar_Syntax_Syntax.withinfo
            (FStar_Syntax_Syntax.Pat_dot_term (a, FStar_Syntax_Syntax.tun)) r
        else FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_var a) r in
      match p.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
          let pats1 =
            FStar_List.map
              (fun uu___ ->
                 match uu___ with
                 | (p1, imp) ->
                     let uu___1 = elaborate_pat env p1 in (uu___1, imp)) pats in
          let uu___ =
            FStar_TypeChecker_Env.lookup_datacon env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu___ with
           | (uu___1, t) ->
               let uu___2 = FStar_Syntax_Util.arrow_formals t in
               (match uu___2 with
                | (f, uu___3) ->
                    let rec aux formals pats2 =
                      match (formals, pats2) with
                      | ([], []) -> []
                      | ([], uu___4::uu___5) ->
                          let uu___6 =
                            FStar_Ident.range_of_lid
                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_TooManyPatternArguments,
                              "Too many pattern arguments") uu___6
                      | (uu___4::uu___5, []) ->
                          FStar_All.pipe_right formals
                            (FStar_List.map
                               (fun fml ->
                                  let uu___6 =
                                    ((fml.FStar_Syntax_Syntax.binder_bv),
                                      (fml.FStar_Syntax_Syntax.binder_qual)) in
                                  match uu___6 with
                                  | (t1, imp) ->
                                      (match imp with
                                       | FStar_Pervasives_Native.Some
                                           (FStar_Syntax_Syntax.Implicit
                                           inaccessible) ->
                                           let a =
                                             let uu___7 =
                                               let uu___8 =
                                                 FStar_Syntax_Syntax.range_of_bv
                                                   t1 in
                                               FStar_Pervasives_Native.Some
                                                 uu___8 in
                                             FStar_Syntax_Syntax.new_bv
                                               uu___7 FStar_Syntax_Syntax.tun in
                                           let r =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let uu___7 =
                                             maybe_dot inaccessible a r in
                                           (uu___7, true)
                                       | uu___7 ->
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStar_Syntax_Print.pat_to_string
                                                   p in
                                               FStar_Util.format1
                                                 "Insufficient pattern arguments (%s)"
                                                 uu___10 in
                                             (FStar_Errors.Fatal_InsufficientPatternArguments,
                                               uu___9) in
                                           let uu___9 =
                                             FStar_Ident.range_of_lid
                                               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           FStar_Errors.raise_error uu___8
                                             uu___9)))
                      | (f1::formals', (p1, p_imp)::pats') ->
                          (match ((f1.FStar_Syntax_Syntax.binder_bv),
                                   (f1.FStar_Syntax_Syntax.binder_qual))
                           with
                           | (uu___4, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible))
                               when inaccessible && p_imp ->
                               (match p1.FStar_Syntax_Syntax.v with
                                | FStar_Syntax_Syntax.Pat_dot_term uu___5 ->
                                    let uu___6 = aux formals' pats' in
                                    (p1, true) :: uu___6
                                | FStar_Syntax_Syntax.Pat_wild uu___5 ->
                                    let a =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (p1.FStar_Syntax_Syntax.p))
                                        FStar_Syntax_Syntax.tun in
                                    let p2 =
                                      let uu___6 =
                                        FStar_Ident.range_of_lid
                                          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                      maybe_dot inaccessible a uu___6 in
                                    let uu___6 = aux formals' pats' in
                                    (p2, true) :: uu___6
                                | uu___5 ->
                                    let uu___6 =
                                      let uu___7 =
                                        let uu___8 =
                                          FStar_Syntax_Print.pat_to_string p1 in
                                        FStar_Util.format1
                                          "This pattern (%s) binds an inaccesible argument; use a wildcard ('_') pattern"
                                          uu___8 in
                                      (FStar_Errors.Fatal_InsufficientPatternArguments,
                                        uu___7) in
                                    FStar_Errors.raise_error uu___6
                                      p1.FStar_Syntax_Syntax.p)
                           | (uu___4, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit uu___5)) when
                               p_imp ->
                               let uu___6 = aux formals' pats' in (p1, true)
                                 :: uu___6
                           | (uu___4, FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit inaccessible)) ->
                               let a =
                                 FStar_Syntax_Syntax.new_bv
                                   (FStar_Pervasives_Native.Some
                                      (p1.FStar_Syntax_Syntax.p))
                                   FStar_Syntax_Syntax.tun in
                               let p2 =
                                 let uu___5 =
                                   FStar_Ident.range_of_lid
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                 maybe_dot inaccessible a uu___5 in
                               let uu___5 = aux formals' pats2 in (p2, true)
                                 :: uu___5
                           | (uu___4, imp) ->
                               let uu___5 =
                                 let uu___6 =
                                   FStar_Syntax_Syntax.is_implicit imp in
                                 (p1, uu___6) in
                               let uu___6 = aux formals' pats' in uu___5 ::
                                 uu___6) in
                    let uu___4 = p in
                    let uu___5 =
                      let uu___6 = let uu___7 = aux f pats1 in (fv, uu___7) in
                      FStar_Syntax_Syntax.Pat_cons uu___6 in
                    {
                      FStar_Syntax_Syntax.v = uu___5;
                      FStar_Syntax_Syntax.p = (uu___4.FStar_Syntax_Syntax.p)
                    }))
      | uu___ -> p
let (pat_as_exp :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.pat ->
          (FStar_Syntax_Syntax.bv Prims.list * FStar_Syntax_Syntax.term *
            FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.pat))
  =
  fun introduce_bv_uvars ->
    fun inst_pat_cons_univs ->
      fun env ->
        fun p ->
          let intro_bv env1 x =
            if Prims.op_Negation introduce_bv_uvars
            then
              ((let uu___ = x in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
                }), FStar_TypeChecker_Env.trivial_guard, env1)
            else
              (let uu___1 = FStar_Syntax_Util.type_u () in
               match uu___1 with
               | (t, uu___2) ->
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Syntax.range_of_bv x in
                     FStar_TypeChecker_Env.new_implicit_var_aux
                       "pattern bv type" uu___4 env1 t
                       FStar_Syntax_Syntax.Allow_untyped
                       FStar_Pervasives_Native.None in
                   (match uu___3 with
                    | (t_x, uu___4, guard) ->
                        let x1 =
                          let uu___5 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___5.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___5.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t_x
                          } in
                        let uu___5 = FStar_TypeChecker_Env.push_bv env1 x1 in
                        (x1, guard, uu___5))) in
          let rec pat_as_arg_with_env env1 p1 =
            match p1.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant c ->
                let e =
                  match c with
                  | FStar_Const.Const_int
                      (repr, FStar_Pervasives_Native.Some sw) ->
                      FStar_ToSyntax_ToSyntax.desugar_machine_integer
                        env1.FStar_TypeChecker_Env.dsenv repr sw
                        p1.FStar_Syntax_Syntax.p
                  | uu___ ->
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_constant c)
                        p1.FStar_Syntax_Syntax.p in
                ([], [], [], env1, e, FStar_TypeChecker_Common.trivial_guard,
                  p1)
            | FStar_Syntax_Syntax.Pat_dot_term (x, uu___) ->
                let uu___1 = FStar_Syntax_Util.type_u () in
                (match uu___1 with
                 | (k, uu___2) ->
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Syntax.range_of_bv x in
                       FStar_TypeChecker_Env.new_implicit_var_aux
                         "pat_dot_term type" uu___4 env1 k
                         FStar_Syntax_Syntax.Allow_ghost
                         FStar_Pervasives_Native.None in
                     (match uu___3 with
                      | (t, uu___4, g) ->
                          let x1 =
                            let uu___5 = x in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___5.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___5.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t
                            } in
                          let uu___5 =
                            let uu___6 = FStar_Syntax_Syntax.range_of_bv x1 in
                            FStar_TypeChecker_Env.new_implicit_var_aux
                              "pat_dot_term" uu___6 env1 t
                              FStar_Syntax_Syntax.Allow_ghost
                              FStar_Pervasives_Native.None in
                          (match uu___5 with
                           | (e, uu___6, g') ->
                               let p2 =
                                 let uu___7 = p1 in
                                 {
                                   FStar_Syntax_Syntax.v =
                                     (FStar_Syntax_Syntax.Pat_dot_term
                                        (x1, e));
                                   FStar_Syntax_Syntax.p =
                                     (uu___7.FStar_Syntax_Syntax.p)
                                 } in
                               let uu___7 =
                                 FStar_TypeChecker_Common.conj_guard g g' in
                               ([], [], [], env1, e, uu___7, p2))))
            | FStar_Syntax_Syntax.Pat_wild x ->
                let uu___ = intro_bv env1 x in
                (match uu___ with
                 | (x1, g, env2) ->
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         p1.FStar_Syntax_Syntax.p in
                     ([x1], [], [x1], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu___ = intro_bv env1 x in
                (match uu___ with
                 | (x1, g, env2) ->
                     let e =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_name x1)
                         p1.FStar_Syntax_Syntax.p in
                     ([x1], [x1], [], env2, e, g, p1))
            | FStar_Syntax_Syntax.Pat_cons (fv, pats) ->
                let uu___ =
                  FStar_All.pipe_right pats
                    (FStar_List.fold_left
                       (fun uu___1 ->
                          fun uu___2 ->
                            match (uu___1, uu___2) with
                            | ((b, a, w, env2, args, guard, pats1),
                               (p2, imp)) ->
                                let uu___3 = pat_as_arg_with_env env2 p2 in
                                (match uu___3 with
                                 | (b', a', w', env3, te, guard', pat) ->
                                     let arg =
                                       if imp
                                       then FStar_Syntax_Syntax.iarg te
                                       else FStar_Syntax_Syntax.as_arg te in
                                     let uu___4 =
                                       FStar_TypeChecker_Common.conj_guard
                                         guard guard' in
                                     ((b' :: b), (a' :: a), (w' :: w), env3,
                                       (arg :: args), uu___4, ((pat, imp) ::
                                       pats1))))
                       ([], [], [], env1, [],
                         FStar_TypeChecker_Common.trivial_guard, [])) in
                (match uu___ with
                 | (b, a, w, env2, args, guard, pats1) ->
                     let hd =
                       let hd1 = FStar_Syntax_Syntax.fv_to_tm fv in
                       if Prims.op_Negation inst_pat_cons_univs
                       then hd1
                       else
                         (let uu___2 =
                            let uu___3 = FStar_Syntax_Syntax.lid_of_fv fv in
                            FStar_TypeChecker_Env.lookup_datacon env2 uu___3 in
                          match uu___2 with
                          | (us, uu___3) ->
                              if (FStar_List.length us) = Prims.int_zero
                              then hd1
                              else FStar_Syntax_Syntax.mk_Tm_uinst hd1 us) in
                     let e =
                       let uu___1 = FStar_All.pipe_right args FStar_List.rev in
                       FStar_Syntax_Syntax.mk_Tm_app hd uu___1
                         p1.FStar_Syntax_Syntax.p in
                     let uu___1 =
                       FStar_All.pipe_right (FStar_List.rev b)
                         FStar_List.flatten in
                     let uu___2 =
                       FStar_All.pipe_right (FStar_List.rev a)
                         FStar_List.flatten in
                     let uu___3 =
                       FStar_All.pipe_right (FStar_List.rev w)
                         FStar_List.flatten in
                     (uu___1, uu___2, uu___3, env2, e, guard,
                       (let uu___4 = p1 in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_cons
                               (fv, (FStar_List.rev pats1)));
                          FStar_Syntax_Syntax.p =
                            (uu___4.FStar_Syntax_Syntax.p)
                        }))) in
          let one_pat env1 p1 =
            let p2 = elaborate_pat env1 p1 in
            let uu___ = pat_as_arg_with_env env1 p2 in
            match uu___ with
            | (b, a, w, env2, arg, guard, p3) ->
                let uu___1 =
                  FStar_All.pipe_right b
                    (FStar_Util.find_dup FStar_Syntax_Syntax.bv_eq) in
                (match uu___1 with
                 | FStar_Pervasives_Native.Some x ->
                     let m = FStar_Syntax_Print.bv_to_string x in
                     let err =
                       let uu___2 =
                         FStar_Util.format1
                           "The pattern variable \"%s\" was used more than once"
                           m in
                       (FStar_Errors.Fatal_NonLinearPatternVars, uu___2) in
                     FStar_Errors.raise_error err p3.FStar_Syntax_Syntax.p
                 | uu___2 -> (b, a, w, arg, guard, p3)) in
          let uu___ = one_pat env p in
          match uu___ with
          | (b, uu___1, uu___2, tm, guard, p1) -> (b, tm, guard, p1)