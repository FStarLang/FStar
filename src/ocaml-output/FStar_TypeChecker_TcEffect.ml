open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun eff_name  ->
      fun comb  ->
        fun n1  ->
          fun uu____58  ->
            match uu____58 with
            | (us,t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t  in
                (match uu____80 with
                 | (us1,t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1
                          in
                       match uu____98 with
                       | (t2,lc,g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                        in
                     (match uu____93 with
                      | (t2,ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2
                             in
                          (match uu____122 with
                           | (g_us,t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty
                                  in
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length
                                          in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int
                                        in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3)
                                        in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156
                                      in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____165 ->
                                        let uu____166 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1  ->
                                                  fun u2  ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2
                                                       in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us)
                                           in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1
                                                  in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us
                                                  in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186)
                                              in
                                           FStar_Errors.raise_error uu____180
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
  
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun reason  ->
        fun r  ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____229 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid
                 in
              FStar_All.pipe_right uu____229 FStar_Util.must  in
            let uu____234 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts  in
            match uu____234 with
            | (uu____239,pure_wp_t) ->
                let uu____241 =
                  let uu____246 =
                    let uu____247 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____247]  in
                  FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____246  in
                uu____241 FStar_Pervasives_Native.None r
             in
          let uu____280 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t
             in
          match uu____280 with
          | (pure_wp_uvar,uu____298,guard_wp) -> (pure_wp_uvar, guard_wp)
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____333 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____333
         then
           let uu____338 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____338
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____356 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____356)
        else ();
        (let log_combinator s uu____385 =
           match uu____385 with
           | (us,t,ty) ->
               let uu____414 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____414
               then
                 let uu____419 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____425 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____419
                   uu____425
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____450 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____450
             (fun uu____467  ->
                match uu____467 with
                | (t,u) ->
                    let uu____478 =
                      let uu____479 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____479
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____478, u))
            in
         let fresh_x_a x a =
           let uu____493 =
             let uu____494 =
               let uu____495 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____495 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____494
              in
           FStar_All.pipe_right uu____493 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           check_and_gen env0 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
            in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____547 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____547 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____571 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____571 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____591 = fresh_a_and_u_a "a"  in
                    (match uu____591 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____612 =
                             let uu____613 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____613
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____612
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____644 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____644  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____649 =
                             let uu____652 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____652
                              in
                           (sig_us, uu____649, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____661 =
            let repr_ts =
              let uu____683 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____683 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____711 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____711 with
            | (repr_us,repr_t,repr_ty) ->
                let underlying_effect_lid =
                  let repr_t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.UnfoldUntil
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_zero);
                      FStar_TypeChecker_Env.AllowUnboundUniverses] env0
                      repr_t
                     in
                  let uu____742 =
                    let uu____743 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____743.FStar_Syntax_Syntax.n  in
                  match uu____742 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____746,t,uu____748) ->
                      let uu____773 =
                        let uu____774 = FStar_Syntax_Subst.compress t  in
                        uu____774.FStar_Syntax_Syntax.n  in
                      (match uu____773 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____777,c) ->
                           let uu____799 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____799
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____802 ->
                           let uu____803 =
                             let uu____809 =
                               let uu____811 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____814 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____811 uu____814
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____809)
                              in
                           FStar_Errors.raise_error uu____803 r)
                  | uu____818 ->
                      let uu____819 =
                        let uu____825 =
                          let uu____827 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____830 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____827 uu____830
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____825)  in
                      FStar_Errors.raise_error uu____819 r
                   in
                ((let uu____835 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____841 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____841)
                     in
                  if uu____835
                  then
                    let uu____844 =
                      let uu____850 =
                        let uu____852 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____855 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____852 uu____855
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____850)
                       in
                    FStar_Errors.raise_error uu____844 r
                  else ());
                 (let uu____862 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____862 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____886 = fresh_a_and_u_a "a"  in
                      (match uu____886 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____912 = signature  in
                               match uu____912 with
                               | (us1,t,uu____927) -> (us1, t)  in
                             let uu____944 =
                               let uu____945 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____945
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____944
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____972 =
                               let uu____975 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____975
                                 (fun uu____988  ->
                                    match uu____988 with
                                    | (t,u1) ->
                                        let uu____995 =
                                          let uu____998 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____998
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____995)
                                in
                             FStar_Syntax_Util.arrow bs uu____972  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1001 =
                               let uu____1014 =
                                 let uu____1017 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1017
                                  in
                               (repr_us, repr_t, uu____1014)  in
                             (uu____1001, underlying_effect_lid))))))
             in
          match uu____661 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1090 = signature  in
                    match uu____1090 with | (us,t,uu____1105) -> (us, t)  in
                  let repr_ts =
                    let uu____1123 = repr  in
                    match uu____1123 with | (us,t,uu____1138) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1188 =
                    let uu____1194 =
                      let uu____1196 = FStar_Util.string_of_int n1  in
                      let uu____1198 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1200 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1196 uu____1198 uu____1200
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1194)  in
                  FStar_Errors.raise_error uu____1188 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1230 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1230 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1258 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1258 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1282 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1282 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1302 = fresh_a_and_u_a "a"  in
                           (match uu____1302 with
                            | (a,u_a) ->
                                let x_a = fresh_x_a "x" a  in
                                let rest_bs =
                                  let uu____1333 =
                                    let uu____1334 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1334.FStar_Syntax_Syntax.n  in
                                  match uu____1333 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1346) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1374 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1374 with
                                       | (a',uu____1384)::(x',uu____1386)::bs1
                                           ->
                                           let uu____1416 =
                                             let uu____1417 =
                                               let uu____1422 =
                                                 let uu____1425 =
                                                   let uu____1426 =
                                                     let uu____1433 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1433)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1426
                                                    in
                                                 [uu____1425]  in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1422
                                                in
                                             FStar_All.pipe_right bs1
                                               uu____1417
                                              in
                                           let uu____1440 =
                                             let uu____1453 =
                                               let uu____1456 =
                                                 let uu____1457 =
                                                   let uu____1464 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          x_a)
                                                      in
                                                   (x', uu____1464)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1457
                                                  in
                                               [uu____1456]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1453
                                              in
                                           FStar_All.pipe_right uu____1416
                                             uu____1440)
                                  | uu____1479 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs = a :: x_a :: rest_bs  in
                                let uu____1503 =
                                  let uu____1508 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1509 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1508 u_a uu____1509  in
                                (match uu____1503 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1529 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1529
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1534 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1534);
                                      (let uu____1535 =
                                         let uu____1538 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1538
                                          in
                                       (ret_us, ret_t, uu____1535))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1565 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1565 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1593 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1593 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1617 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1617 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1637 = fresh_a_and_u_a "a"  in
                            (match uu____1637 with
                             | (a,u_a) ->
                                 let uu____1657 = fresh_a_and_u_a "b"  in
                                 (match uu____1657 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1686 =
                                          let uu____1687 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1687.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1686 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1699) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1727 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1727 with
                                             | (a',uu____1737)::(b',uu____1739)::bs1
                                                 ->
                                                 let uu____1769 =
                                                   let uu____1770 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1770
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1836 =
                                                   let uu____1849 =
                                                     let uu____1852 =
                                                       let uu____1853 =
                                                         let uu____1860 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1860)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1853
                                                        in
                                                     let uu____1867 =
                                                       let uu____1870 =
                                                         let uu____1871 =
                                                           let uu____1878 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1878)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1871
                                                          in
                                                       [uu____1870]  in
                                                     uu____1852 :: uu____1867
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1849
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1769 uu____1836)
                                        | uu____1893 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1917 =
                                        let uu____1928 =
                                          let uu____1933 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1934 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1933 u_a
                                            uu____1934
                                           in
                                        match uu____1928 with
                                        | (repr1,g) ->
                                            let uu____1949 =
                                              let uu____1956 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1956
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1949, g)
                                         in
                                      (match uu____1917 with
                                       | (f,guard_f) ->
                                           let uu____1996 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____2009 =
                                               let uu____2014 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____2033 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____2014 u_b
                                                 uu____2033
                                                in
                                             match uu____2009 with
                                             | (repr1,g) ->
                                                 let uu____2048 =
                                                   let uu____2055 =
                                                     let uu____2056 =
                                                       let uu____2057 =
                                                         let uu____2060 =
                                                           let uu____2063 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____2063
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____2060
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____2057
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____2056
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2055
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____2048, g)
                                              in
                                           (match uu____1996 with
                                            | (g,guard_g) ->
                                                let uu____2115 =
                                                  let uu____2120 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2121 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2120 u_b
                                                    uu____2121
                                                   in
                                                (match uu____2115 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2141 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2141
                                                        in
                                                     let guard_eq =
                                                       FStar_TypeChecker_Rel.teq
                                                         env ty k
                                                        in
                                                     (FStar_List.iter
                                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                                           env)
                                                        [guard_f;
                                                        guard_g;
                                                        guard_repr;
                                                        guard_eq];
                                                      (let uu____2170 =
                                                         let uu____2173 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2173
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2170)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2202 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2202 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2242 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2242 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2267 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2267
                          then
                            let uu____2272 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2278 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2272 uu____2278
                          else ());
                         (let uu____2287 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2287 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2307 = fresh_a_and_u_a "a"  in
                              (match uu____2307 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2336 =
                                       let uu____2337 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2337.FStar_Syntax_Syntax.n  in
                                     match uu____2336 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2349) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2377 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2377 with
                                          | (a',uu____2387)::bs1 ->
                                              let uu____2407 =
                                                let uu____2408 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2408
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2506 =
                                                let uu____2519 =
                                                  let uu____2522 =
                                                    let uu____2523 =
                                                      let uu____2530 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2530)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2523
                                                     in
                                                  [uu____2522]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2519
                                                 in
                                              FStar_All.pipe_right uu____2407
                                                uu____2506)
                                     | uu____2545 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2563 =
                                     let uu____2574 =
                                       let uu____2579 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2580 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2579 u uu____2580
                                        in
                                     match uu____2574 with
                                     | (repr1,g) ->
                                         let uu____2595 =
                                           let uu____2602 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2602
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2595, g)
                                      in
                                   (match uu____2563 with
                                    | (f,guard_f) ->
                                        let uu____2642 =
                                          let uu____2647 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2648 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2647 u
                                            uu____2648
                                           in
                                        (match uu____2642 with
                                         | (ret_t,guard_ret_t) ->
                                             let uu____2665 =
                                               let uu____2670 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               let uu____2671 =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               pure_wp_uvar uu____2670 ret_t
                                                 uu____2671 r
                                                in
                                             (match uu____2665 with
                                              | (pure_wp_uvar1,guard_wp) ->
                                                  let c =
                                                    let uu____2689 =
                                                      let uu____2690 =
                                                        let uu____2691 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2691]  in
                                                      let uu____2692 =
                                                        let uu____2703 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar1
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2703]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2690;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2692;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2689
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2758 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2758
                                                    then
                                                      let uu____2763 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2763
                                                    else ());
                                                   (let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env ty k
                                                       in
                                                    FStar_List.iter
                                                      (FStar_TypeChecker_Rel.force_trivial_guard
                                                         env)
                                                      [guard_f;
                                                      guard_ret_t;
                                                      guard_wp;
                                                      guard_eq];
                                                    (let k1 =
                                                       FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                         env k
                                                        in
                                                     let uu____2771 =
                                                       let uu____2774 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2774
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2771))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2803 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2803 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2831 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2831 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2855 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2855 with
                          | (us,t) ->
                              let uu____2874 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2874 with
                               | (uu____2891,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2894 = fresh_a_and_u_a "a"  in
                                   (match uu____2894 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2923 =
                                            let uu____2924 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2924.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2923 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2936) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2964 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2964 with
                                               | (a',uu____2974)::bs1 ->
                                                   let uu____2994 =
                                                     let uu____2995 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2995
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3093 =
                                                     let uu____3106 =
                                                       let uu____3109 =
                                                         let uu____3110 =
                                                           let uu____3117 =
                                                             let uu____3120 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3120
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3117)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3110
                                                          in
                                                       [uu____3109]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3106
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2994 uu____3093)
                                          | uu____3141 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3159 =
                                          let uu____3170 =
                                            let uu____3175 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3176 =
                                              let uu____3177 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3177
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3175 u_a
                                              uu____3176
                                             in
                                          match uu____3170 with
                                          | (repr1,g) ->
                                              let uu____3198 =
                                                let uu____3205 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3205
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3198, g)
                                           in
                                        (match uu____3159 with
                                         | (f_bs,guard_f) ->
                                             let uu____3245 =
                                               let uu____3256 =
                                                 let uu____3261 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3262 =
                                                   let uu____3263 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3263
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3261 u_a
                                                   uu____3262
                                                  in
                                               match uu____3256 with
                                               | (repr1,g) ->
                                                   let uu____3284 =
                                                     let uu____3291 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3291
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3284, g)
                                                in
                                             (match uu____3245 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3338 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3338
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3346 =
                                                    let uu____3351 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3370 =
                                                      let uu____3371 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3371
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3351
                                                      u_a uu____3370
                                                     in
                                                  (match uu____3346 with
                                                   | (t_body,guard_body) ->
                                                       let k =
                                                         FStar_Syntax_Util.abs
                                                           (FStar_List.append
                                                              bs
                                                              [f_bs;
                                                              g_bs;
                                                              p_b]) t_body
                                                           FStar_Pervasives_Native.None
                                                          in
                                                       let guard_eq =
                                                         FStar_TypeChecker_Rel.teq
                                                           env t k
                                                          in
                                                       (FStar_All.pipe_right
                                                          [guard_f;
                                                          guard_g;
                                                          guard_body;
                                                          guard_eq]
                                                          (FStar_List.iter
                                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                                env));
                                                        (let uu____3431 =
                                                           let uu____3434 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3434
                                                            in
                                                         (if_then_else_us,
                                                           uu____3431,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3445 =
                        let uu____3448 =
                          let uu____3457 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3457 FStar_Util.must  in
                        FStar_All.pipe_right uu____3448
                          FStar_Pervasives_Native.snd
                         in
                      uu____3445.FStar_Syntax_Syntax.pos  in
                    let uu____3518 = if_then_else1  in
                    match uu____3518 with
                    | (ite_us,ite_t,uu____3533) ->
                        let uu____3546 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3546 with
                         | (us,ite_t1) ->
                             let uu____3553 =
                               let uu____3564 =
                                 let uu____3565 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3565.FStar_Syntax_Syntax.n  in
                               match uu____3564 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3579,uu____3580) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3606 =
                                     let uu____3613 =
                                       let uu____3616 =
                                         let uu____3619 =
                                           let uu____3628 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3628
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3619
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3616
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3613
                                       (fun l  ->
                                          let uu____3772 = l  in
                                          match uu____3772 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3606 with
                                    | (f,g,p) ->
                                        let uu____3797 =
                                          let uu____3798 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3798 bs1
                                           in
                                        let uu____3799 =
                                          let uu____3800 =
                                            let uu____3805 =
                                              let uu____3806 =
                                                let uu____3809 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3809
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3806
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3805
                                             in
                                          uu____3800
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3797, uu____3799, f, g, p))
                               | uu____3836 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3553 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3853 =
                                    let uu____3862 = stronger_repr  in
                                    match uu____3862 with
                                    | (uu____3883,subcomp_t,subcomp_ty) ->
                                        let uu____3898 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3898 with
                                         | (uu____3911,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3922 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3922 with
                                               | (uu____3935,subcomp_ty1) ->
                                                   let uu____3937 =
                                                     let uu____3938 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3938.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3937 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3950) ->
                                                        let uu____3971 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3971
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4077 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4095 =
                                                 let uu____4100 =
                                                   let uu____4101 =
                                                     let uu____4104 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4124 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4104 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4101
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4100
                                                  in
                                               uu____4095
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4133 = aux f_t  in
                                             let uu____4136 = aux g_t  in
                                             (uu____4133, uu____4136))
                                     in
                                  (match uu____3853 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4153 =
                                         let aux t =
                                           let uu____4170 =
                                             let uu____4177 =
                                               let uu____4178 =
                                                 let uu____4205 =
                                                   let uu____4222 =
                                                     let uu____4231 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4231
                                                      in
                                                   (uu____4222,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4205,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4178
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4177
                                              in
                                           uu____4170
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4272 = aux subcomp_f  in
                                         let uu____4273 = aux subcomp_g  in
                                         (uu____4272, uu____4273)  in
                                       (match uu____4153 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4277 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4277
                                              then
                                                let uu____4282 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4284 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4282 uu____4284
                                              else ());
                                             (let uu____4289 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4289 with
                                              | (uu____4296,uu____4297,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4300 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4300 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4302 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4302 with
                                                    | (uu____4309,uu____4310,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4316 =
                                                              let uu____4321
                                                                =
                                                                let uu____4322
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4322
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4323
                                                                =
                                                                let uu____4324
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4324]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4321
                                                                uu____4323
                                                               in
                                                            uu____4316
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4357 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4357 g_g
                                                           in
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env g_g1)))))))));
                   (let tc_action env act =
                      let env01 = env  in
                      let r =
                        (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                         in
                      if
                        (FStar_List.length
                           act.FStar_Syntax_Syntax.action_params)
                          <> Prims.int_zero
                      then
                        (let uu____4381 =
                           let uu____4387 =
                             let uu____4389 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4389
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4387)
                            in
                         FStar_Errors.raise_error uu____4381 r)
                      else ();
                      (let uu____4396 =
                         let uu____4401 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4401 with
                         | (usubst,us) ->
                             let uu____4424 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4425 =
                               let uu___426_4426 = act  in
                               let uu____4427 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4428 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___426_4426.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___426_4426.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___426_4426.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4427;
                                 FStar_Syntax_Syntax.action_typ = uu____4428
                               }  in
                             (uu____4424, uu____4425)
                          in
                       match uu____4396 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4432 =
                               let uu____4433 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4433.FStar_Syntax_Syntax.n  in
                             match uu____4432 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4459 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4459
                                 then
                                   let repr_ts =
                                     let uu____4463 = repr  in
                                     match uu____4463 with
                                     | (us,t,uu____4478) -> (us, t)  in
                                   let repr1 =
                                     let uu____4496 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4496
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4508 =
                                       let uu____4513 =
                                         let uu____4514 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4514 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4513
                                        in
                                     uu____4508 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4532 =
                                       let uu____4535 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4535
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4532
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4538 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4539 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4539 with
                            | (act_typ1,uu____4547,g_t) ->
                                let uu____4549 =
                                  let uu____4556 =
                                    let uu___451_4557 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___451_4557.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___451_4557.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___451_4557.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___451_4557.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___451_4557.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___451_4557.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___451_4557.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___451_4557.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___451_4557.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___451_4557.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___451_4557.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___451_4557.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___451_4557.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___451_4557.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___451_4557.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___451_4557.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___451_4557.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___451_4557.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___451_4557.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___451_4557.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___451_4557.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___451_4557.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___451_4557.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___451_4557.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___451_4557.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___451_4557.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___451_4557.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___451_4557.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___451_4557.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___451_4557.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___451_4557.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___451_4557.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___451_4557.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___451_4557.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___451_4557.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___451_4557.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___451_4557.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___451_4557.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___451_4557.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___451_4557.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___451_4557.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___451_4557.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___451_4557.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___451_4557.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4556
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4549 with
                                 | (act_defn,uu____4560,g_d) ->
                                     ((let uu____4563 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4563
                                       then
                                         let uu____4568 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4570 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4568 uu____4570
                                       else ());
                                      (let uu____4575 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4583 =
                                           let uu____4584 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4584.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4583 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4594) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4617 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4617 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4633 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4633 with
                                                   | (a_tm,uu____4653,g_tm)
                                                       ->
                                                       let uu____4667 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4667 with
                                                        | (repr1,g) ->
                                                            let uu____4680 =
                                                              let uu____4683
                                                                =
                                                                let uu____4686
                                                                  =
                                                                  let uu____4689
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4689
                                                                    (
                                                                    fun _4692
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4692)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4686
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4683
                                                               in
                                                            let uu____4693 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4680,
                                                              uu____4693))))
                                         | uu____4696 ->
                                             let uu____4697 =
                                               let uu____4703 =
                                                 let uu____4705 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4705
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4703)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4697 r
                                          in
                                       match uu____4575 with
                                       | (k,g_k) ->
                                           ((let uu____4722 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4722
                                             then
                                               let uu____4727 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4727
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4735 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4735
                                              then
                                                let uu____4740 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4740
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4753 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4753
                                                   in
                                                let repr_args t =
                                                  let uu____4774 =
                                                    let uu____4775 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4775.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4774 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4827 =
                                                        let uu____4828 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4828.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4827 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4837,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4847 ->
                                                           let uu____4848 =
                                                             let uu____4854 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4854)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4848 r)
                                                  | uu____4863 ->
                                                      let uu____4864 =
                                                        let uu____4870 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4870)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4864 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4880 =
                                                  let uu____4881 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4881.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4880 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4906 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4906 with
                                                     | (bs1,c1) ->
                                                         let uu____4913 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4913
                                                          with
                                                          | (us,a,is) ->
                                                              let ct =
                                                                {
                                                                  FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                  FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (
                                                                    ed.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                  FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                  FStar_Syntax_Syntax.flags
                                                                    = []
                                                                }  in
                                                              let uu____4924
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4924))
                                                | uu____4927 ->
                                                    let uu____4928 =
                                                      let uu____4934 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4934)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4928 r
                                                 in
                                              (let uu____4938 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4938
                                               then
                                                 let uu____4943 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4943
                                               else ());
                                              (let act2 =
                                                 let uu____4949 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4949 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___524_4963 =
                                                         act1  in
                                                       let uu____4964 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___524_4963.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___524_4963.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___524_4963.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4964
                                                       }
                                                     else
                                                       (let uu____4967 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4974
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4974
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4967
                                                        then
                                                          let uu___529_4979 =
                                                            act1  in
                                                          let uu____4980 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___529_4979.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___529_4979.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___529_4979.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___529_4979.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4980
                                                          }
                                                        else
                                                          (let uu____4983 =
                                                             let uu____4989 =
                                                               let uu____4991
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4993
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4991
                                                                 uu____4993
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4989)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4983 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5018 =
                      match uu____5018 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5063 =
                        let uu____5064 = tschemes_of repr  in
                        let uu____5069 = tschemes_of return_repr  in
                        let uu____5074 = tschemes_of bind_repr  in
                        let uu____5079 = tschemes_of stronger_repr  in
                        let uu____5084 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5064;
                          FStar_Syntax_Syntax.l_return = uu____5069;
                          FStar_Syntax_Syntax.l_bind = uu____5074;
                          FStar_Syntax_Syntax.l_subcomp = uu____5079;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5084
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5063  in
                    let uu___538_5089 = ed  in
                    let uu____5090 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___538_5089.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___538_5089.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___538_5089.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___538_5089.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5097 = signature  in
                         match uu____5097 with | (us,t,uu____5112) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5090;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___538_5089.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5150 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5150
         then
           let uu____5155 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5155
         else ());
        (let uu____5161 =
           let uu____5166 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5166 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5190 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5190  in
               let uu____5191 =
                 let uu____5198 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5198 bs  in
               (match uu____5191 with
                | (bs1,uu____5204,uu____5205) ->
                    let uu____5206 =
                      let tmp_t =
                        let uu____5216 =
                          let uu____5219 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5224  ->
                                 FStar_Pervasives_Native.Some _5224)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5219
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5216  in
                      let uu____5225 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5225 with
                      | (us,tmp_t1) ->
                          let uu____5242 =
                            let uu____5243 =
                              let uu____5244 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5244
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5243
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5242)
                       in
                    (match uu____5206 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5281 ->
                              let uu____5284 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5291 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5291 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5284
                              then (us, bs2)
                              else
                                (let uu____5302 =
                                   let uu____5308 =
                                     let uu____5310 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5312 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5310 uu____5312
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5308)
                                    in
                                 let uu____5316 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5302
                                   uu____5316))))
            in
         match uu____5161 with
         | (us,bs) ->
             let ed1 =
               let uu___572_5324 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___572_5324.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___572_5324.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___572_5324.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___572_5324.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___572_5324.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___572_5324.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5325 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5325 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5344 =
                    let uu____5349 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5349  in
                  (match uu____5344 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5370 =
                           match uu____5370 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5390 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5390 t  in
                               let uu____5399 =
                                 let uu____5400 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5400 t1  in
                               (us1, uu____5399)
                            in
                         let uu___586_5405 = ed1  in
                         let uu____5406 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5407 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5408 =
                           FStar_List.map
                             (fun a  ->
                                let uu___589_5416 = a  in
                                let uu____5417 =
                                  let uu____5418 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5418  in
                                let uu____5429 =
                                  let uu____5430 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5430  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___589_5416.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___589_5416.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___589_5416.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___589_5416.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5417;
                                  FStar_Syntax_Syntax.action_typ = uu____5429
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___586_5405.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___586_5405.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___586_5405.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___586_5405.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5406;
                           FStar_Syntax_Syntax.combinators = uu____5407;
                           FStar_Syntax_Syntax.actions = uu____5408;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___586_5405.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5442 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5442
                         then
                           let uu____5447 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5447
                         else ());
                        (let env =
                           let uu____5454 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5454
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5489 k =
                           match uu____5489 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5509 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5509 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5518 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5518 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5519 =
                                            let uu____5526 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5526 t1
                                             in
                                          (match uu____5519 with
                                           | (t2,uu____5528,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5531 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5531 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5547 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5549 =
                                                 let uu____5551 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5551
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5547 uu____5549
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5566 ->
                                               let uu____5567 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5574 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5574 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5567
                                               then (g_us, t3)
                                               else
                                                 (let uu____5585 =
                                                    let uu____5591 =
                                                      let uu____5593 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5595 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5593
                                                        uu____5595
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5591)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5585
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5603 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5603
                          then
                            let uu____5608 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5608
                          else ());
                         (let fresh_a_and_wp uu____5624 =
                            let fail1 t =
                              let uu____5637 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5637
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5653 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5653 with
                            | (uu____5664,signature1) ->
                                let uu____5666 =
                                  let uu____5667 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5667.FStar_Syntax_Syntax.n  in
                                (match uu____5666 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5677) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5706)::(wp,uu____5708)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5737 -> fail1 signature1)
                                 | uu____5738 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5752 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5752
                            then
                              let uu____5757 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5757
                            else ()  in
                          let ret_wp =
                            let uu____5763 = fresh_a_and_wp ()  in
                            match uu____5763 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5779 =
                                    let uu____5788 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5795 =
                                      let uu____5804 =
                                        let uu____5811 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5811
                                         in
                                      [uu____5804]  in
                                    uu____5788 :: uu____5795  in
                                  let uu____5830 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5779
                                    uu____5830
                                   in
                                let uu____5833 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5833
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5847 = fresh_a_and_wp ()  in
                             match uu____5847 with
                             | (a,wp_sort_a) ->
                                 let uu____5860 = fresh_a_and_wp ()  in
                                 (match uu____5860 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5876 =
                                          let uu____5885 =
                                            let uu____5892 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5892
                                             in
                                          [uu____5885]  in
                                        let uu____5905 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5876
                                          uu____5905
                                         in
                                      let k =
                                        let uu____5911 =
                                          let uu____5920 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5927 =
                                            let uu____5936 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5943 =
                                              let uu____5952 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5959 =
                                                let uu____5968 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5975 =
                                                  let uu____5984 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5984]  in
                                                uu____5968 :: uu____5975  in
                                              uu____5952 :: uu____5959  in
                                            uu____5936 :: uu____5943  in
                                          uu____5920 :: uu____5927  in
                                        let uu____6027 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5911
                                          uu____6027
                                         in
                                      let uu____6030 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6030
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6044 = fresh_a_and_wp ()  in
                              match uu____6044 with
                              | (a,wp_sort_a) ->
                                  let uu____6057 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6057 with
                                   | (t,uu____6063) ->
                                       let k =
                                         let uu____6067 =
                                           let uu____6076 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6083 =
                                             let uu____6092 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6099 =
                                               let uu____6108 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6108]  in
                                             uu____6092 :: uu____6099  in
                                           uu____6076 :: uu____6083  in
                                         let uu____6139 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6067
                                           uu____6139
                                          in
                                       let uu____6142 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6142
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6156 = fresh_a_and_wp ()  in
                               match uu____6156 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6170 =
                                       let uu____6173 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6173
                                        in
                                     let uu____6174 =
                                       let uu____6175 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6175
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6170
                                       uu____6174
                                      in
                                   let k =
                                     let uu____6187 =
                                       let uu____6196 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6203 =
                                         let uu____6212 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6219 =
                                           let uu____6228 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6235 =
                                             let uu____6244 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6244]  in
                                           uu____6228 :: uu____6235  in
                                         uu____6212 :: uu____6219  in
                                       uu____6196 :: uu____6203  in
                                     let uu____6281 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6187
                                       uu____6281
                                      in
                                   let uu____6284 =
                                     let uu____6289 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6289
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6284
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6321 = fresh_a_and_wp ()  in
                                match uu____6321 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6337 =
                                        let uu____6346 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6353 =
                                          let uu____6362 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6362]  in
                                        uu____6346 :: uu____6353  in
                                      let uu____6387 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6337
                                        uu____6387
                                       in
                                    let uu____6390 =
                                      let uu____6395 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6395
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6390
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6411 = fresh_a_and_wp ()  in
                                 match uu____6411 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6425 =
                                         let uu____6428 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6428
                                          in
                                       let uu____6429 =
                                         let uu____6430 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6430
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6425
                                         uu____6429
                                        in
                                     let wp_sort_b_a =
                                       let uu____6442 =
                                         let uu____6451 =
                                           let uu____6458 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6458
                                            in
                                         [uu____6451]  in
                                       let uu____6471 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6442
                                         uu____6471
                                        in
                                     let k =
                                       let uu____6477 =
                                         let uu____6486 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6493 =
                                           let uu____6502 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6509 =
                                             let uu____6518 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6518]  in
                                           uu____6502 :: uu____6509  in
                                         uu____6486 :: uu____6493  in
                                       let uu____6549 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6477
                                         uu____6549
                                        in
                                     let uu____6552 =
                                       let uu____6557 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6557
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6552
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6573 = fresh_a_and_wp ()  in
                                  match uu____6573 with
                                  | (a,wp_sort_a) ->
                                      let uu____6586 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6586 with
                                       | (t,uu____6592) ->
                                           let k =
                                             let uu____6596 =
                                               let uu____6605 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6612 =
                                                 let uu____6621 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6621]  in
                                               uu____6605 :: uu____6612  in
                                             let uu____6646 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6596 uu____6646
                                              in
                                           let trivial =
                                             let uu____6650 =
                                               let uu____6655 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6655 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6650
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6670 =
                                  let uu____6687 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6687 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6716 ->
                                      let repr =
                                        let uu____6720 = fresh_a_and_wp ()
                                           in
                                        match uu____6720 with
                                        | (a,wp_sort_a) ->
                                            let uu____6733 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6733 with
                                             | (t,uu____6739) ->
                                                 let k =
                                                   let uu____6743 =
                                                     let uu____6752 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6759 =
                                                       let uu____6768 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6768]  in
                                                     uu____6752 :: uu____6759
                                                      in
                                                   let uu____6793 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6743 uu____6793
                                                    in
                                                 let uu____6796 =
                                                   let uu____6801 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6801
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6796
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6845 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6845 with
                                          | (uu____6852,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6855 =
                                                let uu____6862 =
                                                  let uu____6863 =
                                                    let uu____6880 =
                                                      let uu____6891 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6908 =
                                                        let uu____6919 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6919]  in
                                                      uu____6891 ::
                                                        uu____6908
                                                       in
                                                    (repr2, uu____6880)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6863
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6862
                                                 in
                                              uu____6855
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____6985 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____6985 wp  in
                                        let destruct_repr t =
                                          let uu____7000 =
                                            let uu____7001 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7001.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7000 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7012,(t1,uu____7014)::
                                               (wp,uu____7016)::[])
                                              -> (t1, wp)
                                          | uu____7075 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7091 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7091
                                              FStar_Util.must
                                             in
                                          let uu____7118 = fresh_a_and_wp ()
                                             in
                                          match uu____7118 with
                                          | (a,uu____7126) ->
                                              let x_a =
                                                let uu____7132 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7132
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7140 =
                                                    let uu____7145 =
                                                      let uu____7146 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7146
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7155 =
                                                      let uu____7156 =
                                                        let uu____7165 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7165
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7174 =
                                                        let uu____7185 =
                                                          let uu____7194 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7194
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7185]  in
                                                      uu____7156 ::
                                                        uu____7174
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7145 uu____7155
                                                     in
                                                  uu____7140
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7230 =
                                                  let uu____7239 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7246 =
                                                    let uu____7255 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7255]  in
                                                  uu____7239 :: uu____7246
                                                   in
                                                let uu____7280 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7230 uu____7280
                                                 in
                                              let uu____7283 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7283 with
                                               | (k1,uu____7291,uu____7292)
                                                   ->
                                                   let env1 =
                                                     let uu____7296 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7296
                                                      in
                                                   check_and_gen'
                                                     "return_repr"
                                                     Prims.int_one env1
                                                     return_repr_ts
                                                     (FStar_Pervasives_Native.Some
                                                        k1))
                                           in
                                        log_combinator "return_repr"
                                          return_repr;
                                        (let bind_repr =
                                           let bind_repr_ts =
                                             let uu____7309 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7309
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7347 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7347
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7348 = fresh_a_and_wp ()
                                              in
                                           match uu____7348 with
                                           | (a,wp_sort_a) ->
                                               let uu____7361 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7361 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7377 =
                                                        let uu____7386 =
                                                          let uu____7393 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7393
                                                           in
                                                        [uu____7386]  in
                                                      let uu____7406 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7377 uu____7406
                                                       in
                                                    let wp_f =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_f"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a
                                                       in
                                                    let wp_g =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_g"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a_b
                                                       in
                                                    let x_a =
                                                      let uu____7414 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7414
                                                       in
                                                    let wp_g_x =
                                                      let uu____7419 =
                                                        let uu____7424 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7425 =
                                                          let uu____7426 =
                                                            let uu____7435 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7435
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7426]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7424
                                                          uu____7425
                                                         in
                                                      uu____7419
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7466 =
                                                          let uu____7471 =
                                                            let uu____7472 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7472
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7481 =
                                                            let uu____7482 =
                                                              let uu____7485
                                                                =
                                                                let uu____7488
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7489
                                                                  =
                                                                  let uu____7492
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7493
                                                                    =
                                                                    let uu____7496
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7497
                                                                    =
                                                                    let uu____7500
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7500]
                                                                     in
                                                                    uu____7496
                                                                    ::
                                                                    uu____7497
                                                                     in
                                                                  uu____7492
                                                                    ::
                                                                    uu____7493
                                                                   in
                                                                uu____7488 ::
                                                                  uu____7489
                                                                 in
                                                              r :: uu____7485
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7482
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7471
                                                            uu____7481
                                                           in
                                                        uu____7466
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7518 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7518
                                                      then
                                                        let uu____7529 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7536 =
                                                          let uu____7545 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7545]  in
                                                        uu____7529 ::
                                                          uu____7536
                                                      else []  in
                                                    let k =
                                                      let uu____7581 =
                                                        let uu____7590 =
                                                          let uu____7599 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7606 =
                                                            let uu____7615 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7615]  in
                                                          uu____7599 ::
                                                            uu____7606
                                                           in
                                                        let uu____7640 =
                                                          let uu____7649 =
                                                            let uu____7658 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7665 =
                                                              let uu____7674
                                                                =
                                                                let uu____7681
                                                                  =
                                                                  let uu____7682
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7682
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7681
                                                                 in
                                                              let uu____7683
                                                                =
                                                                let uu____7692
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7699
                                                                  =
                                                                  let uu____7708
                                                                    =
                                                                    let uu____7715
                                                                    =
                                                                    let uu____7716
                                                                    =
                                                                    let uu____7725
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7725]
                                                                     in
                                                                    let uu____7744
                                                                    =
                                                                    let uu____7747
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7747
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7716
                                                                    uu____7744
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7715
                                                                     in
                                                                  [uu____7708]
                                                                   in
                                                                uu____7692 ::
                                                                  uu____7699
                                                                 in
                                                              uu____7674 ::
                                                                uu____7683
                                                               in
                                                            uu____7658 ::
                                                              uu____7665
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7649
                                                           in
                                                        FStar_List.append
                                                          uu____7590
                                                          uu____7640
                                                         in
                                                      let uu____7792 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7581 uu____7792
                                                       in
                                                    let uu____7795 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7795 with
                                                     | (k1,uu____7803,uu____7804)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___784_7814
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___784_7814.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7816  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7816)
                                                            in
                                                         check_and_gen'
                                                           "bind_repr"
                                                           (Prims.of_int (2))
                                                           env2 bind_repr_ts
                                                           (FStar_Pervasives_Native.Some
                                                              k1)))
                                            in
                                         log_combinator "bind_repr" bind_repr;
                                         (let actions =
                                            let check_action act =
                                              if
                                                (FStar_List.length
                                                   act.FStar_Syntax_Syntax.action_params)
                                                  <> Prims.int_zero
                                              then
                                                failwith
                                                  "tc_eff_decl: expected action_params to be empty"
                                              else ();
                                              (let uu____7843 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7857 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7857 with
                                                    | (usubst,uvs) ->
                                                        let uu____7880 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7881 =
                                                          let uu___797_7882 =
                                                            act  in
                                                          let uu____7883 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7884 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___797_7882.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___797_7882.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___797_7882.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7883;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7884
                                                          }  in
                                                        (uu____7880,
                                                          uu____7881))
                                                  in
                                               match uu____7843 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7888 =
                                                       let uu____7889 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7889.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7888 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7915 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7915
                                                         then
                                                           let uu____7918 =
                                                             let uu____7921 =
                                                               let uu____7922
                                                                 =
                                                                 let uu____7923
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7923
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7922
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7921
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7918
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7946 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7947 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7947 with
                                                    | (act_typ1,uu____7955,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___814_7958 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___814_7958.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7961 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7961
                                                          then
                                                            let uu____7965 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7967 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7969 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7965
                                                              uu____7967
                                                              uu____7969
                                                          else ());
                                                         (let uu____7974 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7974
                                                          with
                                                          | (act_defn,uu____7982,g_a)
                                                              ->
                                                              let act_defn1 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                  env1
                                                                  act_defn
                                                                 in
                                                              let act_typ2 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                  FStar_TypeChecker_Env.Eager_unfolding;
                                                                  FStar_TypeChecker_Env.Beta]
                                                                  env1
                                                                  act_typ1
                                                                 in
                                                              let uu____7986
                                                                =
                                                                let act_typ3
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    act_typ2
                                                                   in
                                                                match 
                                                                  act_typ3.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8022
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8022
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8034)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8041
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8041
                                                                     in
                                                                    let uu____8044
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8044
                                                                    with
                                                                    | 
                                                                    (k1,uu____8058,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8062
                                                                    ->
                                                                    let uu____8063
                                                                    =
                                                                    let uu____8069
                                                                    =
                                                                    let uu____8071
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8073
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8071
                                                                    uu____8073
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8069)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8063
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____7986
                                                               with
                                                               | (expected_k,g_k)
                                                                   ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                   ((
                                                                    let uu____8091
                                                                    =
                                                                    let uu____8092
                                                                    =
                                                                    let uu____8093
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8093
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8092
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8091);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8095
                                                                    =
                                                                    let uu____8096
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8096.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8095
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8121
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8121
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8128
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8128
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8148
                                                                    =
                                                                    let uu____8149
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8149]
                                                                     in
                                                                    let uu____8150
                                                                    =
                                                                    let uu____8161
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8161]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8148;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8150;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8186
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8186))
                                                                    | 
                                                                    uu____8189
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8191
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8213
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8213))
                                                                     in
                                                                    match uu____8191
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___864_8232
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___864_8232.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___864_8232.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___864_8232.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))
                                               in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action)
                                             in
                                          ((FStar_Pervasives_Native.Some repr),
                                            (FStar_Pervasives_Native.Some
                                               return_repr),
                                            (FStar_Pervasives_Native.Some
                                               bind_repr), actions)))))
                                   in
                                match uu____6670 with
                                | (repr,return_repr,bind_repr,actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts
                                         in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs
                                         in
                                      let uu____8275 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8275 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else1;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp;
                                        FStar_Syntax_Syntax.trivial = trivial;
                                        FStar_Syntax_Syntax.repr = repr;
                                        FStar_Syntax_Syntax.return_repr =
                                          return_repr;
                                        FStar_Syntax_Syntax.bind_repr =
                                          bind_repr
                                      }  in
                                    let combinators1 =
                                      FStar_Syntax_Util.apply_wp_eff_combinators
                                        cl combinators
                                       in
                                    let combinators2 =
                                      match ed2.FStar_Syntax_Syntax.combinators
                                      with
                                      | FStar_Syntax_Syntax.Primitive_eff
                                          uu____8287 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8288 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8289 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___884_8292 = ed2  in
                                      let uu____8293 = cl signature  in
                                      let uu____8294 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___887_8302 = a  in
                                             let uu____8303 =
                                               let uu____8304 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8304
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8329 =
                                               let uu____8330 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8330
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___887_8302.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___887_8302.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___887_8302.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___887_8302.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8303;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8329
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___884_8292.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___884_8292.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___884_8292.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___884_8292.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8293;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8294;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___884_8292.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8356 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8356
                                      then
                                        let uu____8361 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8361
                                      else ());
                                     ed3)))))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      fun quals  ->
        let uu____8387 =
          let uu____8402 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8402 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8387 env ed quals
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail1 uu____8452 =
          let uu____8453 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8459 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8453 uu____8459  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8503)::(wp,uu____8505)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8534 -> fail1 ())
        | uu____8535 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8548 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8548
       then
         let uu____8553 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8553
       else ());
      (let uu____8558 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8558 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           ((let src_ed =
               FStar_TypeChecker_Env.get_effect_decl env0
                 sub1.FStar_Syntax_Syntax.source
                in
             let tgt_ed =
               FStar_TypeChecker_Env.get_effect_decl env0
                 sub1.FStar_Syntax_Syntax.target
                in
             let uu____8591 =
               ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
                  (let uu____8595 =
                     let uu____8596 =
                       FStar_All.pipe_right src_ed
                         FStar_Syntax_Util.get_layered_effect_base
                        in
                     FStar_All.pipe_right uu____8596 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8595
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered)
                     &&
                     (let uu____8605 =
                        let uu____8606 =
                          FStar_All.pipe_right tgt_ed
                            FStar_Syntax_Util.get_layered_effect_base
                           in
                        FStar_All.pipe_right uu____8606 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8605
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8614 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8614))
                in
             if uu____8591
             then
               let uu____8617 =
                 let uu____8623 =
                   let uu____8625 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8628 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8625 uu____8628
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8623)  in
               FStar_Errors.raise_error uu____8617 r
             else ());
            (let uu____8635 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8659 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8659 with
                  | (us1,lift1) ->
                      let uu____8674 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8674, us1, lift1))
                in
             match uu____8635 with
             | (env,us1,lift1) ->
                 let uu____8684 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8684 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8697 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8697
                         then
                           let uu____8702 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8704 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8702 uu____8704
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8718 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8720 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8722 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8718 uu____8720 s uu____8722
                            in
                         let uu____8725 =
                           let uu____8732 =
                             let uu____8737 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8737
                               (fun uu____8754  ->
                                  match uu____8754 with
                                  | (t,u) ->
                                      let uu____8765 =
                                        let uu____8766 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8766
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8765, u))
                              in
                           match uu____8732 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8785 =
                                   let uu____8786 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8786.FStar_Syntax_Syntax.n  in
                                 match uu____8785 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8798) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8826 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8826 with
                                      | (a',uu____8836)::bs1 ->
                                          let uu____8856 =
                                            let uu____8857 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8857
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8955 =
                                            let uu____8968 =
                                              let uu____8971 =
                                                let uu____8972 =
                                                  let uu____8979 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8979)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8972
                                                 in
                                              [uu____8971]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8968
                                             in
                                          FStar_All.pipe_right uu____8856
                                            uu____8955)
                                 | uu____8994 ->
                                     let uu____8995 =
                                       let uu____9001 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____9001)
                                        in
                                     FStar_Errors.raise_error uu____8995 r
                                  in
                               let uu____9013 =
                                 let uu____9024 =
                                   let uu____9029 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____9036 =
                                     let uu____9037 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9037
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____9029 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____9036
                                    in
                                 match uu____9024 with
                                 | (f_sort,g1) ->
                                     let uu____9058 =
                                       let uu____9065 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____9065
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____9058, g1)
                                  in
                               (match uu____9013 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9132 =
                                      let uu____9137 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9138 =
                                        let uu____9139 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9139
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9137 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9138
                                       in
                                    (match uu____9132 with
                                     | (repr,g_repr) ->
                                         let uu____9156 =
                                           let uu____9161 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____9162 =
                                             let uu____9164 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.source
                                                in
                                             let uu____9166 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.target
                                                in
                                             FStar_Util.format2
                                               "implicit for pure_wp in typechecking lift %s~>%s"
                                               uu____9164 uu____9166
                                              in
                                           pure_wp_uvar uu____9161 repr
                                             uu____9162 r
                                            in
                                         (match uu____9156 with
                                          | (pure_wp_uvar1,guard_wp) ->
                                              let c =
                                                let uu____9178 =
                                                  let uu____9179 =
                                                    let uu____9190 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    [uu____9190]  in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = [u_a];
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = repr;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____9179;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  }  in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____9178
                                                 in
                                              let uu____9223 =
                                                FStar_Syntax_Util.arrow bs c
                                                 in
                                              let uu____9226 =
                                                let uu____9227 =
                                                  FStar_TypeChecker_Env.conj_guard
                                                    g_f_b g_repr
                                                   in
                                                FStar_TypeChecker_Env.conj_guard
                                                  uu____9227 guard_wp
                                                 in
                                              (uu____9223, uu____9226))))
                            in
                         match uu____8725 with
                         | (k,g_k) ->
                             ((let uu____9237 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9237
                               then
                                 let uu____9242 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9242
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9251 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9251
                                then
                                  let uu____9256 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9256
                                else ());
                               (let uu____9261 =
                                  let uu____9274 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9274 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9301 =
                                            let uu____9307 =
                                              let uu____9309 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9311 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9313 =
                                                let uu____9315 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9315
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9322 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9309 uu____9311
                                                uu____9313 uu____9322
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9307)
                                             in
                                          FStar_Errors.raise_error uu____9301
                                            r)
                                       else ();
                                       (let uu____9328 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9337 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9337 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9328
                                        then
                                          let uu____9354 =
                                            let uu____9357 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9357
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9354)
                                        else
                                          (let uu____9368 =
                                             let uu____9374 =
                                               let uu____9376 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9378 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9380 =
                                                 let uu____9382 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9382
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9389 =
                                                 let uu____9391 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9391
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9398 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9376 uu____9378
                                                 uu____9380 uu____9389
                                                 uu____9398
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9374)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9368 r)))
                                   in
                                match uu____9261 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___999_9430 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___999_9430.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___999_9430.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9440 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9440
                                      then
                                        let uu____9445 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9445
                                      else ());
                                     sub2)))))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9482 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9482  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9485 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9485
        then tc_layered_lift env sub1
        else
          (let uu____9492 =
             let uu____9499 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9499
              in
           match uu____9492 with
           | (a,wp_a_src) ->
               let uu____9506 =
                 let uu____9513 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9513
                  in
               (match uu____9506 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9521 =
                        let uu____9524 =
                          let uu____9525 =
                            let uu____9532 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9532)  in
                          FStar_Syntax_Syntax.NT uu____9525  in
                        [uu____9524]  in
                      FStar_Syntax_Subst.subst uu____9521 wp_b_tgt  in
                    let expected_k =
                      let uu____9540 =
                        let uu____9549 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9556 =
                          let uu____9565 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9565]  in
                        uu____9549 :: uu____9556  in
                      let uu____9590 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9540 uu____9590  in
                    let repr_type eff_name a1 wp =
                      (let uu____9612 =
                         let uu____9614 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9614  in
                       if uu____9612
                       then
                         let uu____9617 =
                           let uu____9623 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9623)
                            in
                         let uu____9627 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9617 uu____9627
                       else ());
                      (let uu____9630 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9630 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9663 =
                               let uu____9664 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9664
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9663
                              in
                           let uu____9671 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9672 =
                             let uu____9679 =
                               let uu____9680 =
                                 let uu____9697 =
                                   let uu____9708 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9717 =
                                     let uu____9728 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9728]  in
                                   uu____9708 :: uu____9717  in
                                 (repr, uu____9697)  in
                               FStar_Syntax_Syntax.Tm_app uu____9680  in
                             FStar_Syntax_Syntax.mk uu____9679  in
                           uu____9672 FStar_Pervasives_Native.None uu____9671)
                       in
                    let uu____9773 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9946 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9957 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9957 with
                              | (usubst,uvs1) ->
                                  let uu____9980 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9981 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9980, uu____9981)
                            else (env, lift_wp)  in
                          (match uu____9946 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10031 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10031))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10102 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10117 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10117 with
                              | (usubst,uvs) ->
                                  let uu____10142 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10142)
                            else ([], lift)  in
                          (match uu____10102 with
                           | (uvs,lift1) ->
                               ((let uu____10178 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10178
                                 then
                                   let uu____10182 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10182
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10188 =
                                   let uu____10195 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10195 lift1
                                    in
                                 match uu____10188 with
                                 | (lift2,comp,uu____10220) ->
                                     let uu____10221 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10221 with
                                      | (uu____10250,lift_wp,lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp
                                             in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab
                                             in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____10282 =
                                              let uu____10293 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10293
                                               in
                                            let uu____10310 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10282, uu____10310)
                                          else
                                            (let uu____10339 =
                                               let uu____10350 =
                                                 let uu____10359 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10359)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10350
                                                in
                                             let uu____10374 =
                                               let uu____10383 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10383)  in
                                             (uu____10339, uu____10374))))))
                       in
                    (match uu____9773 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1083_10447 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1083_10447.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1083_10447.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1083_10447.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1083_10447.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1083_10447.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1083_10447.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1083_10447.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1083_10447.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1083_10447.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1083_10447.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1083_10447.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1083_10447.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1083_10447.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1083_10447.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1083_10447.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1083_10447.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1083_10447.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1083_10447.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1083_10447.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1083_10447.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1083_10447.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1083_10447.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1083_10447.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1083_10447.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1083_10447.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1083_10447.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1083_10447.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1083_10447.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1083_10447.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1083_10447.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1083_10447.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1083_10447.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1083_10447.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1083_10447.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1083_10447.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1083_10447.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1083_10447.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1083_10447.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1083_10447.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1083_10447.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1083_10447.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1083_10447.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1083_10447.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1083_10447.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10480 =
                                 let uu____10485 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10485 with
                                 | (usubst,uvs1) ->
                                     let uu____10508 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10509 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10508, uu____10509)
                                  in
                               (match uu____10480 with
                                | (env2,lift2) ->
                                    let uu____10514 =
                                      let uu____10521 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10521
                                       in
                                    (match uu____10514 with
                                     | (a1,wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1
                                            in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1
                                            in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a
                                            in
                                         let repr_f =
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ
                                            in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp)
                                              in
                                           let lift_wp_a =
                                             let uu____10547 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10548 =
                                               let uu____10555 =
                                                 let uu____10556 =
                                                   let uu____10573 =
                                                     let uu____10584 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10593 =
                                                       let uu____10604 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10604]  in
                                                     uu____10584 ::
                                                       uu____10593
                                                      in
                                                   (lift_wp1, uu____10573)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10556
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10555
                                                in
                                             uu____10548
                                               FStar_Pervasives_Native.None
                                               uu____10547
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10652 =
                                             let uu____10661 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10668 =
                                               let uu____10677 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10684 =
                                                 let uu____10693 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10693]  in
                                               uu____10677 :: uu____10684  in
                                             uu____10661 :: uu____10668  in
                                           let uu____10724 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10652 uu____10724
                                            in
                                         let uu____10727 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10727 with
                                          | (expected_k2,uu____10737,uu____10738)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10746 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10746))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10754 =
                             let uu____10756 =
                               let uu____10758 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10758
                                 FStar_List.length
                                in
                             uu____10756 <> Prims.int_one  in
                           if uu____10754
                           then
                             let uu____10781 =
                               let uu____10787 =
                                 let uu____10789 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10791 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10793 =
                                   let uu____10795 =
                                     let uu____10797 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10797
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10795
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10789 uu____10791 uu____10793
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10787)
                                in
                             FStar_Errors.raise_error uu____10781 r
                           else ());
                          (let uu____10824 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10827 =
                                  let uu____10829 =
                                    let uu____10832 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10832
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10829
                                    FStar_List.length
                                   in
                                uu____10827 <> Prims.int_one)
                              in
                           if uu____10824
                           then
                             let uu____10871 =
                               let uu____10877 =
                                 let uu____10879 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10881 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10883 =
                                   let uu____10885 =
                                     let uu____10887 =
                                       let uu____10890 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10890
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10887
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10885
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10879 uu____10881 uu____10883
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10877)
                                in
                             FStar_Errors.raise_error uu____10871 r
                           else ());
                          (let uu___1120_10932 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1120_10932.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1120_10932.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           })))))
  
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun uu____10963  ->
      fun r  ->
        match uu____10963 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10986 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11014 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11014 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11045 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11045 c  in
                     let uu____11054 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11054, uvs1, tps1, c1))
               in
            (match uu____10986 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11074 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11074 with
                  | (tps2,c2) ->
                      let uu____11089 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11089 with
                       | (tps3,env3,us) ->
                           let uu____11107 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11107 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11133)::uu____11134 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11153 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11161 =
                                    let uu____11163 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11163  in
                                  if uu____11161
                                  then
                                    let uu____11166 =
                                      let uu____11172 =
                                        let uu____11174 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11176 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11174 uu____11176
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11172)
                                       in
                                    FStar_Errors.raise_error uu____11166 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11184 =
                                    let uu____11185 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11185
                                     in
                                  match uu____11184 with
                                  | (uvs2,t) ->
                                      let uu____11214 =
                                        let uu____11219 =
                                          let uu____11232 =
                                            let uu____11233 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11233.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11232)  in
                                        match uu____11219 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11248,c5)) -> ([], c5)
                                        | (uu____11290,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11329 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11214 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11361 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11361 with
                                               | (uu____11366,t1) ->
                                                   let uu____11368 =
                                                     let uu____11374 =
                                                       let uu____11376 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11378 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11382 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11376
                                                         uu____11378
                                                         uu____11382
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11374)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11368 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env  ->
    fun m  ->
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11424 = FStar_Ident.string_of_lid m  in
              let uu____11426 = FStar_Ident.string_of_lid n1  in
              let uu____11428 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11424 uu____11426
                uu____11428
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            (let uu____11437 =
               FStar_TypeChecker_Env.is_user_reifiable_effect env p  in
             if uu____11437
             then
               let uu____11440 =
                 let uu____11446 =
                   let uu____11448 = FStar_Ident.string_of_lid p  in
                   FStar_Util.format2
                     "Error typechecking the polymonadic bind %s, the final effect %s is reifiable and reification of polymondic binds is not yet implemented"
                     eff_name uu____11448
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____11446)  in
               FStar_Errors.raise_error uu____11440 r
             else ());
            (let uu____11454 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts
                in
             match uu____11454 with
             | (us,t,ty) ->
                 let uu____11470 = FStar_Syntax_Subst.open_univ_vars us ty
                    in
                 (match uu____11470 with
                  | (us1,ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                         in
                      let uu____11482 =
                        let uu____11487 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____11487
                          (fun uu____11504  ->
                             match uu____11504 with
                             | (t1,u) ->
                                 let uu____11515 =
                                   let uu____11516 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t1
                                      in
                                   FStar_All.pipe_right uu____11516
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____11515, u))
                         in
                      (match uu____11482 with
                       | (a,u_a) ->
                           let uu____11524 =
                             let uu____11529 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11529
                               (fun uu____11546  ->
                                  match uu____11546 with
                                  | (t1,u) ->
                                      let uu____11557 =
                                        let uu____11558 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11558
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11557, u))
                              in
                           (match uu____11524 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11575 =
                                    let uu____11576 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11576.FStar_Syntax_Syntax.n  in
                                  match uu____11575 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11588) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11616 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11616 with
                                       | (a',uu____11626)::(b',uu____11628)::bs1
                                           ->
                                           let uu____11658 =
                                             let uu____11659 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11659
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11757 =
                                             let uu____11770 =
                                               let uu____11773 =
                                                 let uu____11774 =
                                                   let uu____11781 =
                                                     let uu____11784 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11784
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11781)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11774
                                                  in
                                               let uu____11797 =
                                                 let uu____11800 =
                                                   let uu____11801 =
                                                     let uu____11808 =
                                                       let uu____11811 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11811
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11808)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11801
                                                    in
                                                 [uu____11800]  in
                                               uu____11773 :: uu____11797  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11770
                                              in
                                           FStar_All.pipe_right uu____11658
                                             uu____11757)
                                  | uu____11832 ->
                                      let uu____11833 =
                                        let uu____11839 =
                                          let uu____11841 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11843 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11841 uu____11843
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11839)
                                         in
                                      FStar_Errors.raise_error uu____11833 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11876 =
                                  let uu____11887 =
                                    let uu____11892 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11893 =
                                      let uu____11894 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11894
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11892 r m u_a uu____11893
                                     in
                                  match uu____11887 with
                                  | (repr,g) ->
                                      let uu____11915 =
                                        let uu____11922 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11922
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11915, g)
                                   in
                                (match uu____11876 with
                                 | (f,guard_f) ->
                                     let uu____11954 =
                                       let x_a =
                                         let uu____11972 =
                                           let uu____11973 =
                                             let uu____11974 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11974
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11973
                                            in
                                         FStar_All.pipe_right uu____11972
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11990 =
                                         let uu____11995 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____12014 =
                                           let uu____12015 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____12015
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11995 r n1 u_b uu____12014
                                          in
                                       match uu____11990 with
                                       | (repr,g) ->
                                           let uu____12036 =
                                             let uu____12043 =
                                               let uu____12044 =
                                                 let uu____12045 =
                                                   let uu____12048 =
                                                     let uu____12051 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12051
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12048
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12045
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12044
                                                in
                                             FStar_All.pipe_right uu____12043
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12036, g)
                                        in
                                     (match uu____11954 with
                                      | (g,guard_g) ->
                                          let uu____12095 =
                                            let uu____12100 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12101 =
                                              let uu____12102 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12102
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12100 r p u_b uu____12101
                                             in
                                          (match uu____12095 with
                                           | (repr,guard_repr) ->
                                               let k =
                                                 let uu____12120 =
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr
                                                     (FStar_Pervasives_Native.Some
                                                        u_b)
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   (FStar_List.append bs
                                                      [f; g]) uu____12120
                                                  in
                                               let guard_eq =
                                                 FStar_TypeChecker_Rel.teq
                                                   env1 ty1 k
                                                  in
                                               (FStar_List.iter
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env1)
                                                  [guard_f;
                                                  guard_g;
                                                  guard_repr;
                                                  guard_eq];
                                                (let uu____12150 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     FStar_Options.Extreme
                                                    in
                                                 if uu____12150
                                                 then
                                                   let uu____12154 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, t)
                                                      in
                                                   let uu____12160 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, k)
                                                      in
                                                   FStar_Util.print3
                                                     "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                     eff_name uu____12154
                                                     uu____12160
                                                 else ());
                                                (let uu____12170 =
                                                   let uu____12176 =
                                                     FStar_Util.format1
                                                       "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                       eff_name
                                                      in
                                                   (FStar_Errors.Warning_BleedingEdge_Feature,
                                                     uu____12176)
                                                    in
                                                 FStar_Errors.log_issue r
                                                   uu____12170);
                                                (let uu____12180 =
                                                   let uu____12181 =
                                                     let uu____12184 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env1)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____12184
                                                       (FStar_Syntax_Subst.close_univ_vars
                                                          us1)
                                                      in
                                                   (us1, uu____12181)  in
                                                 ((us1, t), uu____12180))))))))))
  