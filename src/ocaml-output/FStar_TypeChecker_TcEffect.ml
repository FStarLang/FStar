open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____32 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____32
       then
         let uu____37 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____37
       else ());
      if
        ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
          ||
          ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
             Prims.int_zero)
      then
        (let uu____55 = FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname
            in
         FStar_Errors.raise_error
           (FStar_Errors.Fatal_UnexpectedEffect,
             (Prims.op_Hat "Binders are not supported for layered effects ("
                (Prims.op_Hat (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                   ")"))) uu____55)
      else ();
      (let check_and_gen comb n1 uu____88 =
         match uu____88 with
         | (us,t) ->
             let uu____109 = FStar_Syntax_Subst.open_univ_vars us t  in
             (match uu____109 with
              | (us1,t1) ->
                  let uu____122 =
                    let uu____127 =
                      let uu____134 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term uu____134
                        t1
                       in
                    match uu____127 with
                    | (t2,lc,g) ->
                        (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                         (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                     in
                  (match uu____122 with
                   | (t2,ty) ->
                       let uu____151 =
                         FStar_TypeChecker_Util.generalize_universes env0 t2
                          in
                       (match uu____151 with
                        | (g_us,t3) ->
                            let ty1 =
                              FStar_Syntax_Subst.close_univ_vars g_us ty  in
                            (if (FStar_List.length g_us) <> n1
                             then
                               (let error =
                                  let uu____174 = FStar_Util.string_of_int n1
                                     in
                                  let uu____176 =
                                    let uu____178 =
                                      FStar_All.pipe_right g_us
                                        FStar_List.length
                                       in
                                    FStar_All.pipe_right uu____178
                                      FStar_Util.string_of_int
                                     in
                                  let uu____185 =
                                    FStar_Syntax_Print.tscheme_to_string
                                      (g_us, t3)
                                     in
                                  FStar_Util.format5
                                    "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                    comb uu____174 uu____176 uu____185
                                   in
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                    error) t3.FStar_Syntax_Syntax.pos;
                                (match us1 with
                                 | [] -> ()
                                 | uu____194 ->
                                     let uu____195 =
                                       ((FStar_List.length us1) =
                                          (FStar_List.length g_us))
                                         &&
                                         (FStar_List.forall2
                                            (fun u1  ->
                                               fun u2  ->
                                                 let uu____202 =
                                                   FStar_Syntax_Syntax.order_univ_name
                                                     u1 u2
                                                    in
                                                 uu____202 = Prims.int_zero)
                                            us1 g_us)
                                        in
                                     if uu____195
                                     then ()
                                     else
                                       (let uu____209 =
                                          let uu____215 =
                                            let uu____217 =
                                              FStar_Syntax_Print.univ_names_to_string
                                                us1
                                               in
                                            let uu____219 =
                                              FStar_Syntax_Print.univ_names_to_string
                                                g_us
                                               in
                                            FStar_Util.format4
                                              "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                              (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                              comb uu____217 uu____219
                                             in
                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                            uu____215)
                                           in
                                        FStar_Errors.raise_error uu____209
                                          t3.FStar_Syntax_Syntax.pos)))
                             else ();
                             (g_us, t3, ty1)))))
          in
       let log_combinator s uu____248 =
         match uu____248 with
         | (us,t,ty) ->
             let uu____277 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffects")
                in
             if uu____277
             then
               let uu____282 = FStar_Syntax_Print.tscheme_to_string (us, t)
                  in
               let uu____288 = FStar_Syntax_Print.tscheme_to_string (us, ty)
                  in
               FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____282
                 uu____288
             else ()
          in
       let fresh_a_and_u_a a =
         let uu____313 = FStar_Syntax_Util.type_u ()  in
         FStar_All.pipe_right uu____313
           (fun uu____330  ->
              match uu____330 with
              | (t,u) ->
                  let uu____341 =
                    let uu____342 =
                      FStar_Syntax_Syntax.gen_bv a
                        FStar_Pervasives_Native.None t
                       in
                    FStar_All.pipe_right uu____342
                      FStar_Syntax_Syntax.mk_binder
                     in
                  (uu____341, u))
          in
       let fresh_x_a x a =
         let uu____356 =
           let uu____357 =
             let uu____358 =
               FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
             FStar_All.pipe_right uu____358 FStar_Syntax_Syntax.bv_to_name
              in
           FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
             uu____357
            in
         FStar_All.pipe_right uu____356 FStar_Syntax_Syntax.mk_binder  in
       let signature =
         let r =
           (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
            in
         let uu____385 =
           check_and_gen "signature" Prims.int_one
             ed.FStar_Syntax_Syntax.signature
            in
         match uu____385 with
         | (sig_us,sig_t,sig_ty) ->
             let uu____409 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                in
             (match uu____409 with
              | (us,t) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                  let uu____429 = fresh_a_and_u_a "a"  in
                  (match uu____429 with
                   | (a,u) ->
                       let rest_bs =
                         let uu____450 =
                           let uu____451 =
                             FStar_All.pipe_right a
                               FStar_Pervasives_Native.fst
                              in
                           FStar_All.pipe_right uu____451
                             FStar_Syntax_Syntax.bv_to_name
                            in
                         FStar_TypeChecker_Util.layered_effect_indices_as_binders
                           (sig_us, sig_t) u uu____450
                          in
                       let bs = a :: rest_bs  in
                       let k =
                         let uu____482 =
                           FStar_Syntax_Syntax.mk_Total
                             FStar_Syntax_Syntax.teff
                            in
                         FStar_Syntax_Util.arrow bs uu____482  in
                       let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                       (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                        (let uu____487 =
                           let uu____490 =
                             FStar_All.pipe_right k
                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                  env)
                              in
                           FStar_Syntax_Subst.close_univ_vars us uu____490
                            in
                         (sig_us, uu____487, sig_ty)))))
          in
       log_combinator "signature" signature;
       (let repr =
          let r =
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
             in
          let uu____517 =
            check_and_gen "repr" Prims.int_one ed.FStar_Syntax_Syntax.repr
             in
          match uu____517 with
          | (repr_us,repr_t,repr_ty) ->
              let uu____541 =
                FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
              (match uu____541 with
               | (us,ty) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us  in
                   let uu____561 = fresh_a_and_u_a "a"  in
                   (match uu____561 with
                    | (a,u) ->
                        let rest_bs =
                          let signature_ts =
                            let uu____583 = signature  in
                            match uu____583 with
                            | (us1,t,uu____598) -> (us1, t)  in
                          let uu____615 =
                            let uu____616 =
                              FStar_All.pipe_right a
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____616
                              FStar_Syntax_Syntax.bv_to_name
                             in
                          FStar_TypeChecker_Util.layered_effect_indices_as_binders
                            signature_ts u uu____615
                           in
                        let bs = a :: rest_bs  in
                        let k =
                          let uu____643 =
                            let uu____646 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____646
                              (fun uu____659  ->
                                 match uu____659 with
                                 | (t,u1) ->
                                     let uu____666 =
                                       let uu____669 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some uu____669
                                        in
                                     FStar_Syntax_Syntax.mk_Total' t
                                       uu____666)
                             in
                          FStar_Syntax_Util.arrow bs uu____643  in
                        let g = FStar_TypeChecker_Rel.teq env ty k  in
                        (FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____672 =
                            let uu____675 =
                              FStar_All.pipe_right k
                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                   env)
                               in
                            FStar_Syntax_Subst.close_univ_vars us uu____675
                             in
                          (repr_us, repr_t, uu____672)))))
           in
        log_combinator "repr" repr;
        (let fresh_repr r env u a_tm =
           let signature_ts =
             let uu____710 = signature  in
             match uu____710 with | (us,t,uu____725) -> (us, t)  in
           let repr_ts =
             let uu____743 = repr  in
             match uu____743 with | (us,t,uu____758) -> (us, t)  in
           FStar_TypeChecker_Util.fresh_layered_effect_repr env r
             ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
            in
         let not_an_arrow_error comb n1 t r =
           let uu____808 =
             let uu____814 =
               let uu____816 = FStar_Util.string_of_int n1  in
               let uu____818 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.format4
                 "Type of %s:%s is not an arrow with >= %s binders (%s)"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                 uu____816 uu____818
                in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____814)  in
           FStar_Errors.raise_error uu____808 r  in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____848 =
             check_and_gen "return_repr" Prims.int_one
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____848 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____872 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____872 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____892 = fresh_a_and_u_a "a"  in
                    (match uu____892 with
                     | (a,u_a) ->
                         let rest_bs =
                           let uu____921 =
                             let uu____922 = FStar_Syntax_Subst.compress ty
                                in
                             uu____922.FStar_Syntax_Syntax.n  in
                           match uu____921 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____934) when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____962 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____962 with
                                | (a',uu____972)::bs1 ->
                                    let uu____992 =
                                      let uu____993 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one))
                                         in
                                      FStar_All.pipe_right uu____993
                                        FStar_Pervasives_Native.fst
                                       in
                                    let uu____1059 =
                                      let uu____1072 =
                                        let uu____1075 =
                                          let uu____1076 =
                                            let uu____1083 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a)
                                               in
                                            (a', uu____1083)  in
                                          FStar_Syntax_Syntax.NT uu____1076
                                           in
                                        [uu____1075]  in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1072
                                       in
                                    FStar_All.pipe_right uu____992 uu____1059)
                           | uu____1098 ->
                               not_an_arrow_error "return" (Prims.of_int (2))
                                 ty r
                            in
                         let bs =
                           let uu____1110 =
                             let uu____1119 =
                               let uu____1128 = fresh_x_a "x" a  in
                               [uu____1128]  in
                             FStar_List.append rest_bs uu____1119  in
                           a :: uu____1110  in
                         let uu____1160 =
                           let uu____1165 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____1166 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____1165 u_a uu____1166  in
                         (match uu____1160 with
                          | (repr1,g) ->
                              let k =
                                let uu____1186 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1186  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1191 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1191);
                               (let uu____1192 =
                                  let uu____1195 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env)
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____1195
                                   in
                                (ret_us, ret_t, uu____1192))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1222 =
              check_and_gen "bind_repr" (Prims.of_int (2))
                ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1222 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1246 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1246 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1266 = fresh_a_and_u_a "a"  in
                     (match uu____1266 with
                      | (a,u_a) ->
                          let uu____1286 = fresh_a_and_u_a "b"  in
                          (match uu____1286 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1315 =
                                   let uu____1316 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1316.FStar_Syntax_Syntax.n  in
                                 match uu____1315 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____1328) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____1356 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____1356 with
                                      | (a',uu____1366)::(b',uu____1368)::bs1
                                          ->
                                          let uu____1398 =
                                            let uu____1399 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      (Prims.of_int (2))))
                                               in
                                            FStar_All.pipe_right uu____1399
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____1465 =
                                            let uu____1478 =
                                              let uu____1481 =
                                                let uu____1482 =
                                                  let uu____1489 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____1489)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____1482
                                                 in
                                              let uu____1496 =
                                                let uu____1499 =
                                                  let uu____1500 =
                                                    let uu____1507 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           b)
                                                       in
                                                    (b', uu____1507)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1500
                                                   in
                                                [uu____1499]  in
                                              uu____1481 :: uu____1496  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____1478
                                             in
                                          FStar_All.pipe_right uu____1398
                                            uu____1465)
                                 | uu____1522 ->
                                     not_an_arrow_error "bind"
                                       (Prims.of_int (4)) ty r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1546 =
                                 let uu____1557 =
                                   let uu____1562 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1563 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1562 u_a uu____1563  in
                                 match uu____1557 with
                                 | (repr1,g) ->
                                     let uu____1578 =
                                       let uu____1585 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1585
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1578, g)
                                  in
                               (match uu____1546 with
                                | (f,guard_f) ->
                                    let uu____1625 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1638 =
                                        let uu____1643 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____1662 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____1643 u_b
                                          uu____1662
                                         in
                                      match uu____1638 with
                                      | (repr1,g) ->
                                          let uu____1677 =
                                            let uu____1684 =
                                              let uu____1685 =
                                                let uu____1686 =
                                                  let uu____1689 =
                                                    let uu____1692 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        ()
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____1692
                                                     in
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1 uu____1689
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____1686
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____1685
                                               in
                                            FStar_All.pipe_right uu____1684
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____1677, g)
                                       in
                                    (match uu____1625 with
                                     | (g,guard_g) ->
                                         let uu____1744 =
                                           let uu____1749 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1750 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1749 u_b
                                             uu____1750
                                            in
                                         (match uu____1744 with
                                          | (repr1,guard_repr) ->
                                              let k =
                                                let uu____1770 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____1770
                                                 in
                                              let guard_eq =
                                                FStar_TypeChecker_Rel.teq env
                                                  ty k
                                                 in
                                              (FStar_List.iter
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env)
                                                 [guard_f;
                                                 guard_g;
                                                 guard_repr;
                                                 guard_eq];
                                               (let uu____1799 =
                                                  let uu____1802 =
                                                    FStar_All.pipe_right k
                                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                         env)
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____1802
                                                   in
                                                (bind_us, bind_t, uu____1799)))))))))
             in
          log_combinator "bind_repr" bind_repr;
          (let stronger_repr =
             let stronger_repr =
               FStar_All.pipe_right ed.FStar_Syntax_Syntax.stronger_repr
                 FStar_Util.must
                in
             let r =
               (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                in
             let uu____1854 =
               check_and_gen "stronger_repr" Prims.int_one stronger_repr  in
             match uu____1854 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____1879 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____1879
                   then
                     let uu____1884 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____1890 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____1884 uu____1890
                   else ());
                  (let uu____1899 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____1899 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____1919 = fresh_a_and_u_a "a"  in
                       (match uu____1919 with
                        | (a,u) ->
                            let rest_bs =
                              let uu____1948 =
                                let uu____1949 =
                                  FStar_Syntax_Subst.compress ty  in
                                uu____1949.FStar_Syntax_Syntax.n  in
                              match uu____1948 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1961)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1989 =
                                    FStar_Syntax_Subst.open_binders bs  in
                                  (match uu____1989 with
                                   | (a',uu____1999)::bs1 ->
                                       let uu____2019 =
                                         let uu____2020 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   Prims.int_one))
                                            in
                                         FStar_All.pipe_right uu____2020
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____2118 =
                                         let uu____2131 =
                                           let uu____2134 =
                                             let uu____2135 =
                                               let uu____2142 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      a)
                                                  in
                                               (a', uu____2142)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2135
                                              in
                                           [uu____2134]  in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____2131
                                          in
                                       FStar_All.pipe_right uu____2019
                                         uu____2118)
                              | uu____2157 ->
                                  not_an_arrow_error "stronger"
                                    (Prims.of_int (2)) ty r
                               in
                            let bs = a :: rest_bs  in
                            let uu____2175 =
                              let uu____2186 =
                                let uu____2191 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____2192 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                fresh_repr r uu____2191 u uu____2192  in
                              match uu____2186 with
                              | (repr1,g) ->
                                  let uu____2207 =
                                    let uu____2214 =
                                      FStar_Syntax_Syntax.gen_bv "f"
                                        FStar_Pervasives_Native.None repr1
                                       in
                                    FStar_All.pipe_right uu____2214
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____2207, g)
                               in
                            (match uu____2175 with
                             | (f,guard_f) ->
                                 let uu____2254 =
                                   let uu____2259 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2260 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2259 u uu____2260  in
                                 (match uu____2254 with
                                  | (ret_t,guard_ret_t) ->
                                      let pure_wp_t =
                                        let pure_wp_ts =
                                          let uu____2279 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.pure_wp_lid
                                             in
                                          FStar_All.pipe_right uu____2279
                                            FStar_Util.must
                                           in
                                        let uu____2284 =
                                          FStar_TypeChecker_Env.inst_tscheme
                                            pure_wp_ts
                                           in
                                        match uu____2284 with
                                        | (uu____2289,pure_wp_t) ->
                                            let uu____2291 =
                                              let uu____2296 =
                                                let uu____2297 =
                                                  FStar_All.pipe_right ret_t
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____2297]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                pure_wp_t uu____2296
                                               in
                                            uu____2291
                                              FStar_Pervasives_Native.None r
                                         in
                                      let uu____2330 =
                                        let uu____2343 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          "" r uu____2343 pure_wp_t
                                         in
                                      (match uu____2330 with
                                       | (pure_wp_uvar,uu____2358,guard_wp)
                                           ->
                                           let c =
                                             let uu____2373 =
                                               let uu____2374 =
                                                 let uu____2375 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2375]  in
                                               let uu____2376 =
                                                 let uu____2387 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2387]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2374;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2376;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2373
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2442 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2442
                                             then
                                               let uu____2447 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2447
                                             else ());
                                            (let guard_eq =
                                               FStar_TypeChecker_Rel.teq env
                                                 ty k
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
                                              let uu____2455 =
                                                let uu____2458 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2458
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2455))))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let tc_action env act =
              let r =
                (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                 in
              if
                (FStar_List.length act.FStar_Syntax_Syntax.action_params) <>
                  Prims.int_zero
              then
                (let uu____2491 =
                   let uu____2497 =
                     let uu____2499 =
                       FStar_Syntax_Print.binders_to_string "; "
                         act.FStar_Syntax_Syntax.action_params
                        in
                     FStar_Util.format3
                       "Action %s:%s has non-empty action params (%s)"
                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                       (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                       uu____2499
                      in
                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                     uu____2497)
                    in
                 FStar_Errors.raise_error uu____2491 r)
              else ();
              (let uu____2506 =
                 let uu____2511 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2511 with
                 | (usubst,us) ->
                     let uu____2534 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2535 =
                       let uu___266_2536 = act  in
                       let uu____2537 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2538 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___266_2536.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___266_2536.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___266_2536.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2537;
                         FStar_Syntax_Syntax.action_typ = uu____2538
                       }  in
                     (uu____2534, uu____2535)
                  in
               match uu____2506 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2542 =
                       let uu____2543 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2543.FStar_Syntax_Syntax.n  in
                     match uu____2542 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2569 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2569
                         then
                           let repr_ts =
                             let uu____2573 = repr  in
                             match uu____2573 with
                             | (us,t,uu____2588) -> (us, t)  in
                           let repr1 =
                             let uu____2606 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2606
                               FStar_Pervasives_Native.snd
                              in
                           let repr2 =
                             let uu____2618 =
                               let uu____2623 =
                                 let uu____2624 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 uu____2624 ::
                                   (ct.FStar_Syntax_Syntax.effect_args)
                                  in
                               FStar_Syntax_Syntax.mk_Tm_app repr1 uu____2623
                                in
                             uu____2618 FStar_Pervasives_Native.None r  in
                           let c1 =
                             let uu____2642 =
                               let uu____2645 =
                                 FStar_TypeChecker_Env.new_u_univ ()  in
                               FStar_Pervasives_Native.Some uu____2645  in
                             FStar_Syntax_Syntax.mk_Total' repr2 uu____2642
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____2648 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____2649 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____2649 with
                    | (act_typ1,uu____2657,g_t) ->
                        let uu____2659 =
                          let uu____2666 =
                            let uu___291_2667 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___291_2667.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___291_2667.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___291_2667.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___291_2667.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___291_2667.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___291_2667.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___291_2667.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___291_2667.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___291_2667.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___291_2667.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___291_2667.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___291_2667.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___291_2667.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___291_2667.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___291_2667.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___291_2667.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___291_2667.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___291_2667.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___291_2667.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___291_2667.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___291_2667.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___291_2667.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___291_2667.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___291_2667.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___291_2667.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___291_2667.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___291_2667.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___291_2667.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___291_2667.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___291_2667.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___291_2667.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___291_2667.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___291_2667.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___291_2667.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___291_2667.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___291_2667.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___291_2667.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___291_2667.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___291_2667.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___291_2667.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___291_2667.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___291_2667.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___291_2667.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___291_2667.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____2666 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____2659 with
                         | (act_defn,uu____2670,g_d) ->
                             ((let uu____2673 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____2673
                               then
                                 let uu____2678 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____2680 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____2678 uu____2680
                               else ());
                              (let uu____2685 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____2693 =
                                   let uu____2694 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____2694.FStar_Syntax_Syntax.n  in
                                 match uu____2693 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____2704) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____2727 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____2727 with
                                      | (t,u) ->
                                          let uu____2740 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              "" r env2 t
                                             in
                                          (match uu____2740 with
                                           | (a_tm,uu____2761,g_tm) ->
                                               let uu____2775 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____2775 with
                                                | (repr1,g) ->
                                                    let uu____2788 =
                                                      let uu____2791 =
                                                        let uu____2794 =
                                                          let uu____2797 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2797
                                                            (fun _2800  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _2800)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____2794
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____2791
                                                       in
                                                    let uu____2801 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____2788, uu____2801))))
                                 | uu____2804 ->
                                     let uu____2805 =
                                       let uu____2811 =
                                         let uu____2813 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.format3
                                           "Unexpected non-function type for action %s:%s (%s)"
                                           (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                           uu____2813
                                          in
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         uu____2811)
                                        in
                                     FStar_Errors.raise_error uu____2805 r
                                  in
                               match uu____2685 with
                               | (k,g_k) ->
                                   ((let uu____2830 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____2830
                                     then
                                       let uu____2835 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____2835
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____2843 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____2843
                                      then
                                        let uu____2848 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____2848
                                      else ());
                                     (let act_typ2 =
                                        let err_msg t =
                                          let uu____2861 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          FStar_Util.format3
                                            "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                            (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                            uu____2861
                                           in
                                        let repr_args t =
                                          let uu____2882 =
                                            let uu____2883 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____2883.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2882 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____2935 =
                                                let uu____2936 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____2936.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____2935 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____2945,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____2955 ->
                                                   let uu____2956 =
                                                     let uu____2962 =
                                                       err_msg t  in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____2962)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____2956 r)
                                          | uu____2971 ->
                                              let uu____2972 =
                                                let uu____2978 = err_msg t
                                                   in
                                                (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                  uu____2978)
                                                 in
                                              FStar_Errors.raise_error
                                                uu____2972 r
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____2988 =
                                          let uu____2989 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____2989.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2988 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3014 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3014 with
                                             | (bs1,c1) ->
                                                 let uu____3021 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3021 with
                                                  | (us,a,is) ->
                                                      let ct =
                                                        {
                                                          FStar_Syntax_Syntax.comp_univs
                                                            = us;
                                                          FStar_Syntax_Syntax.effect_name
                                                            =
                                                            (ed.FStar_Syntax_Syntax.mname);
                                                          FStar_Syntax_Syntax.result_typ
                                                            = a;
                                                          FStar_Syntax_Syntax.effect_args
                                                            = is;
                                                          FStar_Syntax_Syntax.flags
                                                            = []
                                                        }  in
                                                      let uu____3032 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3032))
                                        | uu____3035 ->
                                            let uu____3036 =
                                              let uu____3042 = err_msg k1  in
                                              (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                uu____3042)
                                               in
                                            FStar_Errors.raise_error
                                              uu____3036 r
                                         in
                                      (let uu____3046 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3046
                                       then
                                         let uu____3051 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3051
                                       else ());
                                      (let act2 =
                                         if
                                           act1.FStar_Syntax_Syntax.action_univs
                                             = []
                                         then
                                           let uu____3060 =
                                             FStar_TypeChecker_Util.generalize_universes
                                               env1 act_defn
                                              in
                                           match uu____3060 with
                                           | (us,act_defn1) ->
                                               let uu___363_3071 = act1  in
                                               let uu____3072 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___363_3071.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___363_3071.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___363_3071.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3072
                                               }
                                         else
                                           (let uu___365_3075 = act1  in
                                            let uu____3076 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_defn
                                               in
                                            let uu____3077 =
                                              FStar_Syntax_Subst.close_univ_vars
                                                act1.FStar_Syntax_Syntax.action_univs
                                                act_typ2
                                               in
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                =
                                                (uu___365_3075.FStar_Syntax_Syntax.action_name);
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                =
                                                (uu___365_3075.FStar_Syntax_Syntax.action_unqualified_name);
                                              FStar_Syntax_Syntax.action_univs
                                                =
                                                (uu___365_3075.FStar_Syntax_Syntax.action_univs);
                                              FStar_Syntax_Syntax.action_params
                                                =
                                                (uu___365_3075.FStar_Syntax_Syntax.action_params);
                                              FStar_Syntax_Syntax.action_defn
                                                = uu____3076;
                                              FStar_Syntax_Syntax.action_typ
                                                = uu____3077
                                            })
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3097 =
              match uu____3097 with | (a,uu____3113,uu____3114) -> a  in
            let snd1 uu____3146 =
              match uu____3146 with | (uu____3161,b,uu____3163) -> b  in
            let thd uu____3195 =
              match uu____3195 with | (uu____3210,uu____3211,c) -> c  in
            let uu___383_3225 = ed  in
            let uu____3226 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3235  -> FStar_Pervasives_Native.Some _3235)
               in
            let uu____3236 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___383_3225.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___383_3225.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___383_3225.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___383_3225.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___383_3225.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___383_3225.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___383_3225.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3226;
              FStar_Syntax_Syntax.actions = uu____3236;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___383_3225.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3283 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____3283 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3310 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____3310
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____3323 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____3323
       then
         let uu____3328 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____3328
       else ());
      (let uu____3334 =
         let uu____3339 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3339 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____3363 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____3363  in
             let uu____3364 =
               let uu____3371 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____3371 bs  in
             (match uu____3364 with
              | (bs1,uu____3377,uu____3378) ->
                  let uu____3379 =
                    let tmp_t =
                      let uu____3389 =
                        let uu____3392 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _3397  -> FStar_Pervasives_Native.Some _3397)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____3392
                         in
                      FStar_Syntax_Util.arrow bs1 uu____3389  in
                    let uu____3398 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____3398 with
                    | (us,tmp_t1) ->
                        let uu____3415 =
                          let uu____3416 =
                            let uu____3417 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____3417
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____3416
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____3415)
                     in
                  (match uu____3379 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____3486 ->
                            let uu____3489 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____3496 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____3496 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____3489
                            then (us, bs2)
                            else
                              (let uu____3507 =
                                 let uu____3513 =
                                   let uu____3515 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____3517 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____3515 uu____3517
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____3513)
                                  in
                               let uu____3521 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____3507 uu____3521))))
          in
       match uu____3334 with
       | (us,bs) ->
           let ed1 =
             let uu___423_3529 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___423_3529.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___423_3529.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___423_3529.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___423_3529.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___423_3529.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___423_3529.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___423_3529.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___423_3529.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___423_3529.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___423_3529.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___423_3529.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___423_3529.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___423_3529.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___423_3529.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___423_3529.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____3530 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____3530 with
            | (ed_univs_subst,ed_univs) ->
                let uu____3549 =
                  let uu____3554 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____3554  in
                (match uu____3549 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____3575 =
                         match uu____3575 with
                         | (us1,t) ->
                             let t1 =
                               let uu____3595 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3595 t  in
                             let uu____3604 =
                               let uu____3605 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3605 t1  in
                             (us1, uu____3604)
                          in
                       let uu___437_3610 = ed1  in
                       let uu____3611 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____3612 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____3613 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____3614 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____3615 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____3620 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____3623 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____3624 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____3625 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____3626 =
                         FStar_List.map
                           (fun a  ->
                              let uu___440_3634 = a  in
                              let uu____3635 =
                                let uu____3636 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____3636  in
                              let uu____3647 =
                                let uu____3648 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____3648  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___440_3634.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___440_3634.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___440_3634.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___440_3634.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____3635;
                                FStar_Syntax_Syntax.action_typ = uu____3647
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___437_3610.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___437_3610.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___437_3610.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___437_3610.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___437_3610.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____3611;
                         FStar_Syntax_Syntax.ret_wp = uu____3612;
                         FStar_Syntax_Syntax.bind_wp = uu____3613;
                         FStar_Syntax_Syntax.stronger = uu____3614;
                         FStar_Syntax_Syntax.match_wps = uu____3615;
                         FStar_Syntax_Syntax.trivial = uu____3620;
                         FStar_Syntax_Syntax.repr = uu____3623;
                         FStar_Syntax_Syntax.return_repr = uu____3624;
                         FStar_Syntax_Syntax.bind_repr = uu____3625;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____3626;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___437_3610.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____3660 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____3660
                       then
                         let uu____3665 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____3665
                       else ());
                      (let env =
                         let uu____3672 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____3672 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____3707 k =
                         match uu____3707 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____3727 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____3727 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____3736 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____3736 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3737 =
                                          let uu____3744 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____3744 t1
                                           in
                                        (match uu____3737 with
                                         | (t2,uu____3746,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____3749 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____3749 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____3765 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____3767 =
                                               let uu____3769 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3769
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____3765 uu____3767
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____3784 ->
                                             let uu____3785 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____3792 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____3792 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____3785
                                             then (g_us, t3)
                                             else
                                               (let uu____3803 =
                                                  let uu____3809 =
                                                    let uu____3811 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____3813 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____3811
                                                      uu____3813
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____3809)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3803
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____3821 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____3821
                        then
                          let uu____3826 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____3826
                        else ());
                       (let fresh_a_and_wp uu____3842 =
                          let fail1 t =
                            let uu____3855 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____3855
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____3871 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____3871 with
                          | (uu____3882,signature1) ->
                              let uu____3884 =
                                let uu____3885 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____3885.FStar_Syntax_Syntax.n  in
                              (match uu____3884 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____3895) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____3924)::(wp,uu____3926)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____3955 -> fail1 signature1)
                               | uu____3956 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____3970 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____3970
                          then
                            let uu____3975 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____3975
                          else ()  in
                        let ret_wp =
                          let uu____3981 = fresh_a_and_wp ()  in
                          match uu____3981 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____3997 =
                                  let uu____4006 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4013 =
                                    let uu____4022 =
                                      let uu____4029 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4029
                                       in
                                    [uu____4022]  in
                                  uu____4006 :: uu____4013  in
                                let uu____4048 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____3997 uu____4048
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4056 = fresh_a_and_wp ()  in
                           match uu____4056 with
                           | (a,wp_sort_a) ->
                               let uu____4069 = fresh_a_and_wp ()  in
                               (match uu____4069 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4085 =
                                        let uu____4094 =
                                          let uu____4101 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4101
                                           in
                                        [uu____4094]  in
                                      let uu____4114 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4085
                                        uu____4114
                                       in
                                    let k =
                                      let uu____4120 =
                                        let uu____4129 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4136 =
                                          let uu____4145 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4152 =
                                            let uu____4161 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4168 =
                                              let uu____4177 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4184 =
                                                let uu____4193 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4193]  in
                                              uu____4177 :: uu____4184  in
                                            uu____4161 :: uu____4168  in
                                          uu____4145 :: uu____4152  in
                                        uu____4129 :: uu____4136  in
                                      let uu____4236 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4120
                                        uu____4236
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4244 = fresh_a_and_wp ()  in
                            match uu____4244 with
                            | (a,wp_sort_a) ->
                                let uu____4257 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4257 with
                                 | (t,uu____4263) ->
                                     let k =
                                       let uu____4267 =
                                         let uu____4276 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4283 =
                                           let uu____4292 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____4299 =
                                             let uu____4308 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____4308]  in
                                           uu____4292 :: uu____4299  in
                                         uu____4276 :: uu____4283  in
                                       let uu____4339 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4267
                                         uu____4339
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____4351 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____4351 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____4366 = fresh_a_and_wp ()  in
                                   match uu____4366 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____4380 =
                                           let uu____4383 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____4383
                                            in
                                         let uu____4384 =
                                           let uu____4385 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____4385
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____4380 uu____4384
                                          in
                                       let k =
                                         let uu____4397 =
                                           let uu____4406 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____4413 =
                                             let uu____4422 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____4429 =
                                               let uu____4438 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____4445 =
                                                 let uu____4454 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____4454]  in
                                               uu____4438 :: uu____4445  in
                                             uu____4422 :: uu____4429  in
                                           uu____4406 :: uu____4413  in
                                         let uu____4491 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____4397
                                           uu____4491
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____4499 = fresh_a_and_wp ()  in
                                     match uu____4499 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____4515 =
                                             let uu____4524 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4531 =
                                               let uu____4540 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____4540]  in
                                             uu____4524 :: uu____4531  in
                                           let uu____4565 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____4515
                                             uu____4565
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____4573 = fresh_a_and_wp ()  in
                                      match uu____4573 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____4587 =
                                              let uu____4590 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____4590
                                               in
                                            let uu____4591 =
                                              let uu____4592 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____4592
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____4587 uu____4591
                                             in
                                          let wp_sort_b_a =
                                            let uu____4604 =
                                              let uu____4613 =
                                                let uu____4620 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4620
                                                 in
                                              [uu____4613]  in
                                            let uu____4633 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4604 uu____4633
                                             in
                                          let k =
                                            let uu____4639 =
                                              let uu____4648 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4655 =
                                                let uu____4664 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____4671 =
                                                  let uu____4680 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____4680]  in
                                                uu____4664 :: uu____4671  in
                                              uu____4648 :: uu____4655  in
                                            let uu____4711 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4639 uu____4711
                                             in
                                          check_and_gen' "close_wp"
                                            (Prims.of_int (2))
                                            FStar_Pervasives_Native.None
                                            close_wp
                                            (FStar_Pervasives_Native.Some k)
                                       in
                                    log_combinator "close_wp" close_wp1;
                                    FStar_Util.Inl
                                      {
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else2;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp1;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp1
                                      })))
                              in
                           let trivial =
                             let uu____4721 = fresh_a_and_wp ()  in
                             match uu____4721 with
                             | (a,wp_sort_a) ->
                                 let uu____4736 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____4736 with
                                  | (t,uu____4744) ->
                                      let k =
                                        let uu____4748 =
                                          let uu____4757 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4764 =
                                            let uu____4773 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____4773]  in
                                          uu____4757 :: uu____4764  in
                                        let uu____4798 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____4748
                                          uu____4798
                                         in
                                      let trivial =
                                        let uu____4802 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____4802
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____4817 =
                             let uu____4828 =
                               let uu____4829 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____4829.FStar_Syntax_Syntax.n  in
                             match uu____4828 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____4848 ->
                                 let repr =
                                   let uu____4850 = fresh_a_and_wp ()  in
                                   match uu____4850 with
                                   | (a,wp_sort_a) ->
                                       let uu____4863 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____4863 with
                                        | (t,uu____4869) ->
                                            let k =
                                              let uu____4873 =
                                                let uu____4882 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4889 =
                                                  let uu____4898 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____4898]  in
                                                uu____4882 :: uu____4889  in
                                              let uu____4923 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4873 uu____4923
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____4943 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____4943 with
                                     | (uu____4950,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____4953 =
                                           let uu____4960 =
                                             let uu____4961 =
                                               let uu____4978 =
                                                 let uu____4989 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5006 =
                                                   let uu____5017 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5017]  in
                                                 uu____4989 :: uu____5006  in
                                               (repr2, uu____4978)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____4961
                                              in
                                           FStar_Syntax_Syntax.mk uu____4960
                                            in
                                         uu____4953
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5083 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5083 wp  in
                                   let destruct_repr t =
                                     let uu____5098 =
                                       let uu____5099 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5099.FStar_Syntax_Syntax.n  in
                                     match uu____5098 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5110,(t1,uu____5112)::
                                          (wp,uu____5114)::[])
                                         -> (t1, wp)
                                     | uu____5173 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5184 = fresh_a_and_wp ()  in
                                     match uu____5184 with
                                     | (a,uu____5192) ->
                                         let x_a =
                                           let uu____5198 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5198
                                            in
                                         let res =
                                           let wp =
                                             let uu____5206 =
                                               let uu____5211 =
                                                 let uu____5212 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5212
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5221 =
                                                 let uu____5222 =
                                                   let uu____5231 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5231
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5240 =
                                                   let uu____5251 =
                                                     let uu____5260 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5260
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5251]  in
                                                 uu____5222 :: uu____5240  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5211 uu____5221
                                                in
                                             uu____5206
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____5296 =
                                             let uu____5305 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5312 =
                                               let uu____5321 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____5321]  in
                                             uu____5305 :: uu____5312  in
                                           let uu____5346 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____5296
                                             uu____5346
                                            in
                                         let uu____5349 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____5349 with
                                          | (k1,uu____5357,uu____5358) ->
                                              let env1 =
                                                let uu____5362 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5362
                                                 in
                                              check_and_gen' "return_repr"
                                                Prims.int_one env1
                                                ed2.FStar_Syntax_Syntax.return_repr
                                                (FStar_Pervasives_Native.Some
                                                   k1))
                                      in
                                   log_combinator "return_repr" return_repr;
                                   (let bind_repr =
                                      let r =
                                        let uu____5373 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____5373
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____5374 = fresh_a_and_wp ()  in
                                      match uu____5374 with
                                      | (a,wp_sort_a) ->
                                          let uu____5387 = fresh_a_and_wp ()
                                             in
                                          (match uu____5387 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____5403 =
                                                   let uu____5412 =
                                                     let uu____5419 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5419
                                                      in
                                                   [uu____5412]  in
                                                 let uu____5432 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5403 uu____5432
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
                                                 let uu____5440 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____5440
                                                  in
                                               let wp_g_x =
                                                 let uu____5445 =
                                                   let uu____5450 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____5451 =
                                                     let uu____5452 =
                                                       let uu____5461 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5461
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5452]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____5450 uu____5451
                                                    in
                                                 uu____5445
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____5492 =
                                                     let uu____5497 =
                                                       let uu____5498 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5498
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____5507 =
                                                       let uu____5508 =
                                                         let uu____5511 =
                                                           let uu____5514 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____5515 =
                                                             let uu____5518 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____5519 =
                                                               let uu____5522
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____5523
                                                                 =
                                                                 let uu____5526
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____5526]
                                                                  in
                                                               uu____5522 ::
                                                                 uu____5523
                                                                in
                                                             uu____5518 ::
                                                               uu____5519
                                                              in
                                                           uu____5514 ::
                                                             uu____5515
                                                            in
                                                         r :: uu____5511  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____5508
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5497 uu____5507
                                                      in
                                                   uu____5492
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____5544 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____5544
                                                 then
                                                   let uu____5555 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____5562 =
                                                     let uu____5571 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____5571]  in
                                                   uu____5555 :: uu____5562
                                                 else []  in
                                               let k =
                                                 let uu____5607 =
                                                   let uu____5616 =
                                                     let uu____5625 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____5632 =
                                                       let uu____5641 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____5641]  in
                                                     uu____5625 :: uu____5632
                                                      in
                                                   let uu____5666 =
                                                     let uu____5675 =
                                                       let uu____5684 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____5691 =
                                                         let uu____5700 =
                                                           let uu____5707 =
                                                             let uu____5708 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____5708
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____5707
                                                            in
                                                         let uu____5709 =
                                                           let uu____5718 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____5725 =
                                                             let uu____5734 =
                                                               let uu____5741
                                                                 =
                                                                 let uu____5742
                                                                   =
                                                                   let uu____5751
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____5751]
                                                                    in
                                                                 let uu____5770
                                                                   =
                                                                   let uu____5773
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5773
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____5742
                                                                   uu____5770
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____5741
                                                                in
                                                             [uu____5734]  in
                                                           uu____5718 ::
                                                             uu____5725
                                                            in
                                                         uu____5700 ::
                                                           uu____5709
                                                          in
                                                       uu____5684 ::
                                                         uu____5691
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____5675
                                                      in
                                                   FStar_List.append
                                                     uu____5616 uu____5666
                                                    in
                                                 let uu____5818 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5607 uu____5818
                                                  in
                                               let uu____5821 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____5821 with
                                                | (k1,uu____5829,uu____5830)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___638_5842 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___638_5842.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _5844  ->
                                                           FStar_Pervasives_Native.Some
                                                             _5844)
                                                       in
                                                    check_and_gen'
                                                      "bind_repr"
                                                      (Prims.of_int (2)) env2
                                                      ed2.FStar_Syntax_Syntax.bind_repr
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
                                         (let uu____5871 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____5885 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____5885 with
                                               | (usubst,uvs) ->
                                                   let uu____5908 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____5909 =
                                                     let uu___651_5910 = act
                                                        in
                                                     let uu____5911 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____5912 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___651_5910.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___651_5910.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___651_5910.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____5911;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5912
                                                     }  in
                                                   (uu____5908, uu____5909))
                                             in
                                          match uu____5871 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____5916 =
                                                  let uu____5917 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____5917.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5916 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____5943 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____5943
                                                    then
                                                      let uu____5946 =
                                                        let uu____5949 =
                                                          let uu____5950 =
                                                            let uu____5951 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5951
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____5950
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____5949
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____5946
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____5974 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____5975 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____5975 with
                                               | (act_typ1,uu____5983,g_t) ->
                                                   let env' =
                                                     let uu___668_5986 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___668_5986.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____5989 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____5989
                                                     then
                                                       let uu____5993 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____5995 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____5997 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____5993
                                                         uu____5995
                                                         uu____5997
                                                     else ());
                                                    (let uu____6002 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6002 with
                                                     | (act_defn,uu____6010,g_a)
                                                         ->
                                                         let act_defn1 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant]
                                                             env1 act_defn
                                                            in
                                                         let act_typ2 =
                                                           FStar_TypeChecker_Normalize.normalize
                                                             [FStar_TypeChecker_Env.UnfoldUntil
                                                                FStar_Syntax_Syntax.delta_constant;
                                                             FStar_TypeChecker_Env.Eager_unfolding;
                                                             FStar_TypeChecker_Env.Beta]
                                                             env1 act_typ1
                                                            in
                                                         let uu____6014 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6050
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6050
                                                                with
                                                                | (bs2,uu____6062)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6069
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6069
                                                                     in
                                                                    let uu____6072
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6072
                                                                    with
                                                                    | 
                                                                    (k1,uu____6086,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6090 ->
                                                               let uu____6091
                                                                 =
                                                                 let uu____6097
                                                                   =
                                                                   let uu____6099
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6101
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6099
                                                                    uu____6101
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6097)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6091
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6014
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6119
                                                                  =
                                                                  let uu____6120
                                                                    =
                                                                    let uu____6121
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6121
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6120
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6119);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6123
                                                                    =
                                                                    let uu____6124
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6124.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6123
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6149
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6149
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6156
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6156
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6176
                                                                    =
                                                                    let uu____6177
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6177]
                                                                     in
                                                                    let uu____6178
                                                                    =
                                                                    let uu____6189
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6189]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6176;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6178;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6214
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6214))
                                                                  | uu____6217
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6219
                                                                  =
                                                                  if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                  then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                  else
                                                                    (
                                                                    let uu____6241
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6241))
                                                                   in
                                                                match uu____6219
                                                                with
                                                                | (univs1,act_defn2)
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
                                                                    let uu___718_6260
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___718_6260.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___718_6260.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___718_6260.FStar_Syntax_Syntax.action_params);
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
                                     (repr, return_repr, bind_repr, actions)))))
                              in
                           match uu____4817 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6285 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6285
                                   ts1
                                  in
                               let ed3 =
                                 let uu___730_6295 = ed2  in
                                 let uu____6296 = cl signature  in
                                 let uu____6297 = cl ret_wp  in
                                 let uu____6298 = cl bind_wp  in
                                 let uu____6299 = cl stronger  in
                                 let uu____6300 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____6305 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____6308 = cl repr  in
                                 let uu____6309 = cl return_repr  in
                                 let uu____6310 = cl bind_repr  in
                                 let uu____6311 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___733_6319 = a  in
                                        let uu____6320 =
                                          let uu____6321 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____6321
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____6346 =
                                          let uu____6347 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____6347
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___733_6319.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___733_6319.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___733_6319.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___733_6319.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____6320;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____6346
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___730_6295.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___730_6295.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___730_6295.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___730_6295.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___730_6295.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____6296;
                                   FStar_Syntax_Syntax.ret_wp = uu____6297;
                                   FStar_Syntax_Syntax.bind_wp = uu____6298;
                                   FStar_Syntax_Syntax.stronger = uu____6299;
                                   FStar_Syntax_Syntax.match_wps = uu____6300;
                                   FStar_Syntax_Syntax.trivial = uu____6305;
                                   FStar_Syntax_Syntax.repr = uu____6308;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____6309;
                                   FStar_Syntax_Syntax.bind_repr = uu____6310;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____6311;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___730_6295.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____6373 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6373
                                 then
                                   let uu____6378 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____6378
                                 else ());
                                ed3))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      (if ed.FStar_Syntax_Syntax.is_layered
       then tc_layered_eff_decl
       else tc_non_layered_eff_decl) env ed
  
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
        let fail1 uu____6431 =
          let uu____6432 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____6438 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____6432 uu____6438  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____6482)::(wp,uu____6484)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____6513 -> fail1 ())
        | uu____6514 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____6527 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____6527
       then
         let uu____6532 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____6532
       else ());
      (let uu____6537 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____6537 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           (if (FStar_List.length us) <> Prims.int_zero
            then
              (let uu____6571 =
                 let uu____6573 = FStar_Syntax_Print.sub_eff_to_string sub1
                    in
                 Prims.op_Hat
                   "Unexpected number of universes in typechecking %s"
                   uu____6573
                  in
               failwith uu____6571)
            else ();
            (let uu____6578 =
               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env0 lift  in
             match uu____6578 with
             | (lift1,lc,g) ->
                 (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                  (let lift_ty =
                     FStar_All.pipe_right lc.FStar_TypeChecker_Common.res_typ
                       (FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.Beta] env0)
                      in
                   (let uu____6595 =
                      FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                        (FStar_Options.Other "LayeredEffects")
                       in
                    if uu____6595
                    then
                      let uu____6600 =
                        FStar_Syntax_Print.term_to_string lift1  in
                      let uu____6602 =
                        FStar_Syntax_Print.term_to_string lift_ty  in
                      FStar_Util.print2
                        "Typechecked lift: %s and lift_ty: %s\n" uu____6600
                        uu____6602
                    else ());
                   (let uu____6607 =
                      let uu____6614 =
                        let uu____6619 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____6619
                          (fun uu____6636  ->
                             match uu____6636 with
                             | (t,u) ->
                                 let uu____6647 =
                                   let uu____6648 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____6648
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____6647, u))
                         in
                      match uu____6614 with
                      | (a,u_a) ->
                          let uu____6658 =
                            let uu____6665 =
                              FStar_TypeChecker_Env.lookup_effect_lid env0
                                sub1.FStar_Syntax_Syntax.source
                               in
                            monad_signature env0
                              sub1.FStar_Syntax_Syntax.source uu____6665
                             in
                          (match uu____6658 with
                           | (a',wp_sort_a') ->
                               let src_wp_sort_a =
                                 let uu____6679 =
                                   let uu____6682 =
                                     let uu____6683 =
                                       let uu____6690 =
                                         let uu____6693 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____6693
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       (a', uu____6690)  in
                                     FStar_Syntax_Syntax.NT uu____6683  in
                                   [uu____6682]  in
                                 FStar_Syntax_Subst.subst uu____6679
                                   wp_sort_a'
                                  in
                               let wp =
                                 let uu____6713 =
                                   FStar_Syntax_Syntax.gen_bv "wp"
                                     FStar_Pervasives_Native.None
                                     src_wp_sort_a
                                    in
                                 FStar_All.pipe_right uu____6713
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let rest_bs =
                                 let uu____6730 =
                                   let uu____6731 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____6731.FStar_Syntax_Syntax.n  in
                                 match uu____6730 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____6743) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (3))
                                     ->
                                     let uu____6771 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____6771 with
                                      | (a'1,uu____6781)::(wp',uu____6783)::bs1
                                          ->
                                          let uu____6813 =
                                            FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one) bs1
                                             in
                                          (match uu____6813 with
                                           | (bs2,uu____6856) ->
                                               let substs =
                                                 let uu____6892 =
                                                   let uu____6893 =
                                                     let uu____6900 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a'1, uu____6900)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____6893
                                                    in
                                                 let uu____6907 =
                                                   let uu____6910 =
                                                     let uu____6911 =
                                                       let uu____6918 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              wp)
                                                          in
                                                       (wp', uu____6918)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____6911
                                                      in
                                                   [uu____6910]  in
                                                 uu____6892 :: uu____6907  in
                                               FStar_Syntax_Subst.subst_binders
                                                 substs bs2)
                                      | uu____6925 -> failwith "Impossible!")
                                 | uu____6935 ->
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_UnexpectedEffect,
                                         "") r
                                  in
                               let f =
                                 let f_sort =
                                   let uu____6956 =
                                     let uu____6965 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_Syntax_Syntax.t_unit
                                        in
                                     [uu____6965]  in
                                   let uu____6984 =
                                     let uu____6987 =
                                       let uu____6988 =
                                         let uu____6991 =
                                           FStar_All.pipe_right a
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_All.pipe_right uu____6991
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       let uu____7002 =
                                         let uu____7013 =
                                           let uu____7022 =
                                             let uu____7023 =
                                               FStar_All.pipe_right wp
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____7023
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_All.pipe_right uu____7022
                                             FStar_Syntax_Syntax.as_arg
                                            in
                                         [uu____7013]  in
                                       {
                                         FStar_Syntax_Syntax.comp_univs =
                                           [u_a];
                                         FStar_Syntax_Syntax.effect_name =
                                           (sub1.FStar_Syntax_Syntax.source);
                                         FStar_Syntax_Syntax.result_typ =
                                           uu____6988;
                                         FStar_Syntax_Syntax.effect_args =
                                           uu____7002;
                                         FStar_Syntax_Syntax.flags = []
                                       }  in
                                     FStar_Syntax_Syntax.mk_Comp uu____6987
                                      in
                                   FStar_Syntax_Util.arrow uu____6956
                                     uu____6984
                                    in
                                 let uu____7056 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort
                                    in
                                 FStar_All.pipe_right uu____7056
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               let bs = a :: wp ::
                                 (FStar_List.append rest_bs [f])  in
                               let uu____7103 =
                                 let uu____7108 =
                                   FStar_TypeChecker_Env.push_binders env0 bs
                                    in
                                 let uu____7109 =
                                   let uu____7110 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____7110
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                   uu____7108 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____7109
                                  in
                               (match uu____7103 with
                                | (repr,g_repr) ->
                                    let uu____7127 =
                                      let uu____7130 =
                                        let uu____7133 =
                                          let uu____7136 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_All.pipe_right uu____7136
                                            (fun _7139  ->
                                               FStar_Pervasives_Native.Some
                                                 _7139)
                                           in
                                        FStar_Syntax_Syntax.mk_Total' repr
                                          uu____7133
                                         in
                                      FStar_Syntax_Util.arrow bs uu____7130
                                       in
                                    (uu____7127, g_repr)))
                       in
                    match uu____6607 with
                    | (k,g_k) ->
                        ((let uu____7149 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____7149
                          then
                            let uu____7154 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "Before unification k: %s\n"
                              uu____7154
                          else ());
                         (let g1 = FStar_TypeChecker_Rel.teq env0 lift_ty k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env0 g1;
                          (let uu____7163 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____7163
                           then
                             let uu____7168 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____7168
                           else ());
                          (let uu____7173 =
                             FStar_TypeChecker_Util.generalize_universes env0
                               lift1
                              in
                           match uu____7173 with
                           | (us1,lift2) ->
                               let lift_wp =
                                 let uu____7187 =
                                   let uu____7188 =
                                     let uu____7193 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us1
                                        in
                                     FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       uu____7193
                                      in
                                   FStar_All.pipe_right k uu____7188  in
                                 FStar_All.pipe_right uu____7187
                                   (FStar_Syntax_Subst.close_univ_vars us1)
                                  in
                               let sub2 =
                                 let uu___830_7197 = sub1  in
                                 {
                                   FStar_Syntax_Syntax.source =
                                     (uu___830_7197.FStar_Syntax_Syntax.source);
                                   FStar_Syntax_Syntax.target =
                                     (uu___830_7197.FStar_Syntax_Syntax.target);
                                   FStar_Syntax_Syntax.lift_wp =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift_wp));
                                   FStar_Syntax_Syntax.lift =
                                     (FStar_Pervasives_Native.Some
                                        (us1, lift2))
                                 }  in
                               ((let uu____7207 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env0)
                                     (FStar_Options.Other "LayeredEffects")
                                    in
                                 if uu____7207
                                 then
                                   let uu____7212 =
                                     FStar_Syntax_Print.sub_eff_to_string
                                       sub2
                                      in
                                   FStar_Util.print1 "Final sub_effect: %s\n"
                                     uu____7212
                                 else ());
                                sub2))))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        if
          ed_src.FStar_Syntax_Syntax.is_layered ||
            ed_tgt.FStar_Syntax_Syntax.is_layered
        then tc_layered_lift env sub1
        else
          (let uu____7238 =
             let uu____7245 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____7245
              in
           match uu____7238 with
           | (a,wp_a_src) ->
               let uu____7252 =
                 let uu____7259 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7259
                  in
               (match uu____7252 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7267 =
                        let uu____7270 =
                          let uu____7271 =
                            let uu____7278 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7278)  in
                          FStar_Syntax_Syntax.NT uu____7271  in
                        [uu____7270]  in
                      FStar_Syntax_Subst.subst uu____7267 wp_b_tgt  in
                    let expected_k =
                      let uu____7286 =
                        let uu____7295 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7302 =
                          let uu____7311 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7311]  in
                        uu____7295 :: uu____7302  in
                      let uu____7336 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7286 uu____7336  in
                    let repr_type eff_name a1 wp =
                      (let uu____7358 =
                         let uu____7360 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____7360  in
                       if uu____7358
                       then
                         let uu____7363 =
                           let uu____7369 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____7369)
                            in
                         let uu____7373 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____7363 uu____7373
                       else ());
                      (let uu____7376 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____7376 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____7409 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____7410 =
                             let uu____7417 =
                               let uu____7418 =
                                 let uu____7435 =
                                   let uu____7446 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____7455 =
                                     let uu____7466 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____7466]  in
                                   uu____7446 :: uu____7455  in
                                 (repr, uu____7435)  in
                               FStar_Syntax_Syntax.Tm_app uu____7418  in
                             FStar_Syntax_Syntax.mk uu____7417  in
                           uu____7410 FStar_Pervasives_Native.None uu____7409)
                       in
                    let uu____7511 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____7684 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____7695 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____7695 with
                              | (usubst,uvs1) ->
                                  let uu____7718 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____7719 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____7718, uu____7719)
                            else (env, lift_wp)  in
                          (match uu____7684 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____7769 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____7769))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____7840 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____7855 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____7855 with
                              | (usubst,uvs) ->
                                  let uu____7880 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____7880)
                            else ([], lift)  in
                          (match uu____7840 with
                           | (uvs,lift1) ->
                               ((let uu____7916 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7916
                                 then
                                   let uu____7920 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____7920
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____7926 =
                                   let uu____7933 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____7933 lift1
                                    in
                                 match uu____7926 with
                                 | (lift2,comp,uu____7958) ->
                                     let uu____7959 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____7959 with
                                      | (uu____7988,lift_wp,lift_elab) ->
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
                                            let uu____8020 =
                                              let uu____8031 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8031
                                               in
                                            let uu____8048 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8020, uu____8048)
                                          else
                                            (let uu____8077 =
                                               let uu____8088 =
                                                 let uu____8097 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8097)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8088
                                                in
                                             let uu____8112 =
                                               let uu____8121 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8121)  in
                                             (uu____8077, uu____8112))))))
                       in
                    (match uu____7511 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___910_8185 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___910_8185.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___910_8185.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___910_8185.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___910_8185.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___910_8185.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___910_8185.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___910_8185.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___910_8185.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___910_8185.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___910_8185.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___910_8185.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___910_8185.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___910_8185.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___910_8185.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___910_8185.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___910_8185.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___910_8185.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___910_8185.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___910_8185.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___910_8185.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___910_8185.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___910_8185.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___910_8185.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___910_8185.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___910_8185.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___910_8185.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___910_8185.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___910_8185.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___910_8185.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___910_8185.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___910_8185.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___910_8185.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___910_8185.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___910_8185.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___910_8185.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___910_8185.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___910_8185.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___910_8185.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___910_8185.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___910_8185.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___910_8185.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___910_8185.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___910_8185.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___910_8185.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8218 =
                                 let uu____8223 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8223 with
                                 | (usubst,uvs1) ->
                                     let uu____8246 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8247 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8246, uu____8247)
                                  in
                               (match uu____8218 with
                                | (env2,lift2) ->
                                    let uu____8252 =
                                      let uu____8259 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8259
                                       in
                                    (match uu____8252 with
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
                                             let uu____8285 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8286 =
                                               let uu____8293 =
                                                 let uu____8294 =
                                                   let uu____8311 =
                                                     let uu____8322 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8331 =
                                                       let uu____8342 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8342]  in
                                                     uu____8322 :: uu____8331
                                                      in
                                                   (lift_wp1, uu____8311)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8294
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8293
                                                in
                                             uu____8286
                                               FStar_Pervasives_Native.None
                                               uu____8285
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8390 =
                                             let uu____8399 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8406 =
                                               let uu____8415 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8422 =
                                                 let uu____8431 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8431]  in
                                               uu____8415 :: uu____8422  in
                                             uu____8399 :: uu____8406  in
                                           let uu____8462 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8390
                                             uu____8462
                                            in
                                         let uu____8465 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8465 with
                                          | (expected_k2,uu____8475,uu____8476)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____8484 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8484))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8492 =
                             let uu____8494 =
                               let uu____8496 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8496
                                 FStar_List.length
                                in
                             uu____8494 <> Prims.int_one  in
                           if uu____8492
                           then
                             let uu____8519 =
                               let uu____8525 =
                                 let uu____8527 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8529 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8531 =
                                   let uu____8533 =
                                     let uu____8535 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8535
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8533
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8527 uu____8529 uu____8531
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8525)
                                in
                             FStar_Errors.raise_error uu____8519 r
                           else ());
                          (let uu____8562 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8565 =
                                  let uu____8567 =
                                    let uu____8570 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8570
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8567
                                    FStar_List.length
                                   in
                                uu____8565 <> Prims.int_one)
                              in
                           if uu____8562
                           then
                             let uu____8608 =
                               let uu____8614 =
                                 let uu____8616 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8618 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8620 =
                                   let uu____8622 =
                                     let uu____8624 =
                                       let uu____8627 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____8627
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8624
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8622
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8616 uu____8618 uu____8620
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8614)
                                in
                             FStar_Errors.raise_error uu____8608 r
                           else ());
                          (let uu___947_8669 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___947_8669.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___947_8669.FStar_Syntax_Syntax.target);
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
    fun uu____8700  ->
      fun r  ->
        match uu____8700 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____8723 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____8751 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____8751 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____8782 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____8782 c  in
                     let uu____8791 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____8791, uvs1, tps1, c1))
               in
            (match uu____8723 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____8811 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____8811 with
                  | (tps2,c2) ->
                      let uu____8826 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____8826 with
                       | (tps3,env3,us) ->
                           let uu____8844 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____8844 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____8870)::uu____8871 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____8890 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____8898 =
                                    let uu____8900 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____8900  in
                                  if uu____8898
                                  then
                                    let uu____8903 =
                                      let uu____8909 =
                                        let uu____8911 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____8913 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____8911 uu____8913
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____8909)
                                       in
                                    FStar_Errors.raise_error uu____8903 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____8921 =
                                    let uu____8922 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____8922
                                     in
                                  match uu____8921 with
                                  | (uvs2,t) ->
                                      let uu____8951 =
                                        let uu____8956 =
                                          let uu____8969 =
                                            let uu____8970 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____8970.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____8969)  in
                                        match uu____8956 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____8985,c5)) -> ([], c5)
                                        | (uu____9027,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____9066 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____8951 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____9098 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____9098 with
                                               | (uu____9103,t1) ->
                                                   let uu____9105 =
                                                     let uu____9111 =
                                                       let uu____9113 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____9115 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____9119 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____9113
                                                         uu____9115
                                                         uu____9119
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____9111)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____9105 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  