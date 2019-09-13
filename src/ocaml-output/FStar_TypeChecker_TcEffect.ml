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
                           env r ed.FStar_Syntax_Syntax.mname (sig_us, sig_t)
                           u uu____450
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
                            env r ed.FStar_Syntax_Syntax.mname signature_ts u
                            uu____615
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
             let uu____1844 =
               check_and_gen "stronger_repr" Prims.int_one stronger_repr  in
             match uu____1844 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____1869 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____1869
                   then
                     let uu____1874 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____1880 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____1874 uu____1880
                   else ());
                  (let uu____1889 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____1889 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____1909 = fresh_a_and_u_a "a"  in
                       (match uu____1909 with
                        | (a,u) ->
                            let rest_bs =
                              let uu____1938 =
                                let uu____1939 =
                                  FStar_Syntax_Subst.compress ty  in
                                uu____1939.FStar_Syntax_Syntax.n  in
                              match uu____1938 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1951)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1979 =
                                    FStar_Syntax_Subst.open_binders bs  in
                                  (match uu____1979 with
                                   | (a',uu____1989)::bs1 ->
                                       let uu____2009 =
                                         let uu____2010 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   Prims.int_one))
                                            in
                                         FStar_All.pipe_right uu____2010
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____2108 =
                                         let uu____2121 =
                                           let uu____2124 =
                                             let uu____2125 =
                                               let uu____2132 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      a)
                                                  in
                                               (a', uu____2132)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2125
                                              in
                                           [uu____2124]  in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____2121
                                          in
                                       FStar_All.pipe_right uu____2009
                                         uu____2108)
                              | uu____2147 ->
                                  not_an_arrow_error "stronger"
                                    (Prims.of_int (2)) ty r
                               in
                            let bs = a :: rest_bs  in
                            let uu____2165 =
                              let uu____2176 =
                                let uu____2181 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____2182 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                fresh_repr r uu____2181 u uu____2182  in
                              match uu____2176 with
                              | (repr1,g) ->
                                  let uu____2197 =
                                    let uu____2204 =
                                      FStar_Syntax_Syntax.gen_bv "f"
                                        FStar_Pervasives_Native.None repr1
                                       in
                                    FStar_All.pipe_right uu____2204
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____2197, g)
                               in
                            (match uu____2165 with
                             | (f,guard_f) ->
                                 let uu____2244 =
                                   let uu____2249 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2250 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2249 u uu____2250  in
                                 (match uu____2244 with
                                  | (ret_t,guard_ret_t) ->
                                      let pure_wp_t =
                                        let pure_wp_ts =
                                          let uu____2269 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.pure_wp_lid
                                             in
                                          FStar_All.pipe_right uu____2269
                                            FStar_Util.must
                                           in
                                        let uu____2274 =
                                          FStar_TypeChecker_Env.inst_tscheme
                                            pure_wp_ts
                                           in
                                        match uu____2274 with
                                        | (uu____2279,pure_wp_t) ->
                                            let uu____2281 =
                                              let uu____2286 =
                                                let uu____2287 =
                                                  FStar_All.pipe_right ret_t
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____2287]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                pure_wp_t uu____2286
                                               in
                                            uu____2281
                                              FStar_Pervasives_Native.None r
                                         in
                                      let uu____2320 =
                                        let reason =
                                          FStar_Util.format1
                                            "implicit for pure_wp in checking stronger for %s"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           in
                                        let uu____2336 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          reason r uu____2336 pure_wp_t
                                         in
                                      (match uu____2320 with
                                       | (pure_wp_uvar,uu____2350,guard_wp)
                                           ->
                                           let c =
                                             let uu____2365 =
                                               let uu____2366 =
                                                 let uu____2367 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2367]  in
                                               let uu____2368 =
                                                 let uu____2379 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2379]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2366;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2368;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2365
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2434 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2434
                                             then
                                               let uu____2439 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2439
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
                                              let uu____2447 =
                                                let uu____2450 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2450
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2447))))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let conjunction =
              let conjunction_ts =
                let uu____2475 =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.match_wps
                    FStar_Util.right
                   in
                uu____2475.FStar_Syntax_Syntax.conjunction  in
              let r =
                (FStar_Pervasives_Native.snd conjunction_ts).FStar_Syntax_Syntax.pos
                 in
              let uu____2485 =
                check_and_gen "conjunction" Prims.int_one conjunction_ts  in
              match uu____2485 with
              | (conjunction_us,conjunction_t,conjunction_ty) ->
                  let uu____2509 =
                    FStar_Syntax_Subst.open_univ_vars conjunction_us
                      conjunction_t
                     in
                  (match uu____2509 with
                   | (us,t) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____2529 = fresh_a_and_u_a "a"  in
                       (match uu____2529 with
                        | (a,u_a) ->
                            let signature_ts =
                              let uu____2550 = signature  in
                              match uu____2550 with
                              | (us1,t1,uu____2565) -> (us1, t1)  in
                            let f_bs =
                              let uu____2583 =
                                let uu____2584 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2584
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                env r ed.FStar_Syntax_Syntax.mname
                                signature_ts u_a uu____2583
                               in
                            let g_bs =
                              let uu____2594 =
                                let uu____2595 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2595
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                env r ed.FStar_Syntax_Syntax.mname
                                signature_ts u_a uu____2594
                               in
                            let p_b =
                              let uu____2611 =
                                FStar_Syntax_Syntax.gen_bv "p"
                                  (FStar_Pervasives_Native.Some r)
                                  FStar_Syntax_Util.ktype0
                                 in
                              FStar_All.pipe_right uu____2611
                                FStar_Syntax_Syntax.mk_binder
                               in
                            let bs = a ::
                              (FStar_List.append f_bs
                                 (FStar_List.append g_bs [p_b]))
                               in
                            let uu____2658 =
                              let uu____2663 =
                                FStar_TypeChecker_Env.push_binders env bs  in
                              let uu____2664 =
                                let uu____2665 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____2665
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              fresh_repr r uu____2663 u_a uu____2664  in
                            (match uu____2658 with
                             | (t_body,guard_body) ->
                                 let k =
                                   FStar_Syntax_Util.abs bs t_body
                                     FStar_Pervasives_Native.None
                                    in
                                 let guard_eq =
                                   FStar_TypeChecker_Rel.teq env t k  in
                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                    env guard_body;
                                  FStar_TypeChecker_Rel.force_trivial_guard
                                    env guard_eq;
                                  (let uu____2694 =
                                     let uu____2697 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env)
                                        in
                                     FStar_Syntax_Subst.close_univ_vars
                                       conjunction_us uu____2697
                                      in
                                   (conjunction_us, uu____2694,
                                     conjunction_ty))))))
               in
            log_combinator "conjunction" conjunction;
            (let tc_action env act =
               let env01 = env  in
               let r =
                 (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                  in
               if
                 (FStar_List.length act.FStar_Syntax_Syntax.action_params) <>
                   Prims.int_zero
               then
                 (let uu____2729 =
                    let uu____2735 =
                      let uu____2737 =
                        FStar_Syntax_Print.binders_to_string "; "
                          act.FStar_Syntax_Syntax.action_params
                         in
                      FStar_Util.format3
                        "Action %s:%s has non-empty action params (%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                        (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                        uu____2737
                       in
                    (FStar_Errors.Fatal_MalformedActionDeclaration,
                      uu____2735)
                     in
                  FStar_Errors.raise_error uu____2729 r)
               else ();
               (let uu____2744 =
                  let uu____2749 =
                    FStar_Syntax_Subst.univ_var_opening
                      act.FStar_Syntax_Syntax.action_univs
                     in
                  match uu____2749 with
                  | (usubst,us) ->
                      let uu____2772 =
                        FStar_TypeChecker_Env.push_univ_vars env us  in
                      let uu____2773 =
                        let uu___299_2774 = act  in
                        let uu____2775 =
                          FStar_Syntax_Subst.subst usubst
                            act.FStar_Syntax_Syntax.action_defn
                           in
                        let uu____2776 =
                          FStar_Syntax_Subst.subst usubst
                            act.FStar_Syntax_Syntax.action_typ
                           in
                        {
                          FStar_Syntax_Syntax.action_name =
                            (uu___299_2774.FStar_Syntax_Syntax.action_name);
                          FStar_Syntax_Syntax.action_unqualified_name =
                            (uu___299_2774.FStar_Syntax_Syntax.action_unqualified_name);
                          FStar_Syntax_Syntax.action_univs = us;
                          FStar_Syntax_Syntax.action_params =
                            (uu___299_2774.FStar_Syntax_Syntax.action_params);
                          FStar_Syntax_Syntax.action_defn = uu____2775;
                          FStar_Syntax_Syntax.action_typ = uu____2776
                        }  in
                      (uu____2772, uu____2773)
                   in
                match uu____2744 with
                | (env1,act1) ->
                    let act_typ =
                      let uu____2780 =
                        let uu____2781 =
                          FStar_Syntax_Subst.compress
                            act1.FStar_Syntax_Syntax.action_typ
                           in
                        uu____2781.FStar_Syntax_Syntax.n  in
                      match uu____2780 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                          let uu____2807 =
                            FStar_Ident.lid_equals
                              ct.FStar_Syntax_Syntax.effect_name
                              ed.FStar_Syntax_Syntax.mname
                             in
                          if uu____2807
                          then
                            let repr_ts =
                              let uu____2811 = repr  in
                              match uu____2811 with
                              | (us,t,uu____2826) -> (us, t)  in
                            let repr1 =
                              let uu____2844 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                 in
                              FStar_All.pipe_right uu____2844
                                FStar_Pervasives_Native.snd
                               in
                            let repr2 =
                              let uu____2856 =
                                let uu____2861 =
                                  let uu____2862 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ
                                     in
                                  uu____2862 ::
                                    (ct.FStar_Syntax_Syntax.effect_args)
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____2861
                                 in
                              uu____2856 FStar_Pervasives_Native.None r  in
                            let c1 =
                              let uu____2880 =
                                let uu____2883 =
                                  FStar_TypeChecker_Env.new_u_univ ()  in
                                FStar_Pervasives_Native.Some uu____2883  in
                              FStar_Syntax_Syntax.mk_Total' repr2 uu____2880
                               in
                            FStar_Syntax_Util.arrow bs c1
                          else act1.FStar_Syntax_Syntax.action_typ
                      | uu____2886 -> act1.FStar_Syntax_Syntax.action_typ  in
                    let uu____2887 =
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                        act_typ
                       in
                    (match uu____2887 with
                     | (act_typ1,uu____2895,g_t) ->
                         let uu____2897 =
                           let uu____2904 =
                             let uu___324_2905 =
                               FStar_TypeChecker_Env.set_expected_typ env1
                                 act_typ1
                                in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___324_2905.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___324_2905.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___324_2905.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___324_2905.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___324_2905.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___324_2905.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___324_2905.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___324_2905.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___324_2905.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___324_2905.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___324_2905.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp = false;
                               FStar_TypeChecker_Env.effects =
                                 (uu___324_2905.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___324_2905.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___324_2905.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___324_2905.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___324_2905.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___324_2905.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___324_2905.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___324_2905.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___324_2905.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___324_2905.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___324_2905.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___324_2905.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___324_2905.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___324_2905.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___324_2905.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___324_2905.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___324_2905.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___324_2905.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___324_2905.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___324_2905.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___324_2905.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___324_2905.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___324_2905.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___324_2905.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___324_2905.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___324_2905.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___324_2905.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___324_2905.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___324_2905.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___324_2905.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___324_2905.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___324_2905.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___324_2905.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___324_2905.FStar_TypeChecker_Env.erasable_types_tab)
                             }  in
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                             uu____2904 act1.FStar_Syntax_Syntax.action_defn
                            in
                         (match uu____2897 with
                          | (act_defn,uu____2908,g_d) ->
                              ((let uu____2911 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____2911
                                then
                                  let uu____2916 =
                                    FStar_Syntax_Print.term_to_string
                                      act_defn
                                     in
                                  let uu____2918 =
                                    FStar_Syntax_Print.term_to_string
                                      act_typ1
                                     in
                                  FStar_Util.print2
                                    "Typechecked action definition: %s and action type: %s\n"
                                    uu____2916 uu____2918
                                else ());
                               (let uu____2923 =
                                  let act_typ2 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1
                                      act_typ1
                                     in
                                  let uu____2931 =
                                    let uu____2932 =
                                      FStar_Syntax_Subst.compress act_typ2
                                       in
                                    uu____2932.FStar_Syntax_Syntax.n  in
                                  match uu____2931 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____2942) ->
                                      let bs1 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      let env2 =
                                        FStar_TypeChecker_Env.push_binders
                                          env1 bs1
                                         in
                                      let uu____2965 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____2965 with
                                       | (t,u) ->
                                           let reason =
                                             FStar_Util.format2
                                               "implicit for return type of action %s:%s"
                                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                              in
                                           let uu____2981 =
                                             FStar_TypeChecker_Util.new_implicit_var
                                               reason r env2 t
                                              in
                                           (match uu____2981 with
                                            | (a_tm,uu____3001,g_tm) ->
                                                let uu____3015 =
                                                  fresh_repr r env2 u a_tm
                                                   in
                                                (match uu____3015 with
                                                 | (repr1,g) ->
                                                     let uu____3028 =
                                                       let uu____3031 =
                                                         let uu____3034 =
                                                           let uu____3037 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3037
                                                             (fun _3040  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _3040)
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____3034
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         bs1 uu____3031
                                                        in
                                                     let uu____3041 =
                                                       FStar_TypeChecker_Env.conj_guard
                                                         g g_tm
                                                        in
                                                     (uu____3028, uu____3041))))
                                  | uu____3044 ->
                                      let uu____3045 =
                                        let uu____3051 =
                                          let uu____3053 =
                                            FStar_Syntax_Print.term_to_string
                                              act_typ2
                                             in
                                          FStar_Util.format3
                                            "Unexpected non-function type for action %s:%s (%s)"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                            (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                            uu____3053
                                           in
                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                          uu____3051)
                                         in
                                      FStar_Errors.raise_error uu____3045 r
                                   in
                                match uu____2923 with
                                | (k,g_k) ->
                                    ((let uu____3070 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3070
                                      then
                                        let uu____3075 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type: %s\n"
                                          uu____3075
                                      else ());
                                     (let g =
                                        FStar_TypeChecker_Rel.teq env1
                                          act_typ1 k
                                         in
                                      FStar_List.iter
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1) [g_t; g_d; g_k; g];
                                      (let uu____3083 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3083
                                       then
                                         let uu____3088 =
                                           FStar_Syntax_Print.term_to_string
                                             k
                                            in
                                         FStar_Util.print1
                                           "Expected action type after unification: %s\n"
                                           uu____3088
                                       else ());
                                      (let act_typ2 =
                                         let err_msg t =
                                           let uu____3101 =
                                             FStar_Syntax_Print.term_to_string
                                               t
                                              in
                                           FStar_Util.format3
                                             "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                             uu____3101
                                            in
                                         let repr_args t =
                                           let uu____3122 =
                                             let uu____3123 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____3123.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3122 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (head1,a::is) ->
                                               let uu____3175 =
                                                 let uu____3176 =
                                                   FStar_Syntax_Subst.compress
                                                     head1
                                                    in
                                                 uu____3176.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____3175 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (uu____3185,us) ->
                                                    (us,
                                                      (FStar_Pervasives_Native.fst
                                                         a), is)
                                                | uu____3195 ->
                                                    let uu____3196 =
                                                      let uu____3202 =
                                                        err_msg t  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____3202)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3196 r)
                                           | uu____3211 ->
                                               let uu____3212 =
                                                 let uu____3218 = err_msg t
                                                    in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____3218)
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3212 r
                                            in
                                         let k1 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 k
                                            in
                                         let uu____3228 =
                                           let uu____3229 =
                                             FStar_Syntax_Subst.compress k1
                                              in
                                           uu____3229.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3228 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,c) ->
                                             let uu____3254 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs c
                                                in
                                             (match uu____3254 with
                                              | (bs1,c1) ->
                                                  let uu____3261 =
                                                    repr_args
                                                      (FStar_Syntax_Util.comp_result
                                                         c1)
                                                     in
                                                  (match uu____3261 with
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
                                                       let uu____3272 =
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           ct
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         bs1 uu____3272))
                                         | uu____3275 ->
                                             let uu____3276 =
                                               let uu____3282 = err_msg k1
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____3282)
                                                in
                                             FStar_Errors.raise_error
                                               uu____3276 r
                                          in
                                       (let uu____3286 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffects")
                                           in
                                        if uu____3286
                                        then
                                          let uu____3291 =
                                            FStar_Syntax_Print.term_to_string
                                              act_typ2
                                             in
                                          FStar_Util.print1
                                            "Action type after injecting it into the monad: %s\n"
                                            uu____3291
                                        else ());
                                       (let act2 =
                                          let uu____3297 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env1 act_defn
                                             in
                                          match uu____3297 with
                                          | (us,act_defn1) ->
                                              if
                                                act1.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then
                                                let uu___397_3311 = act1  in
                                                let uu____3312 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    us act_typ2
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.action_name
                                                    =
                                                    (uu___397_3311.FStar_Syntax_Syntax.action_name);
                                                  FStar_Syntax_Syntax.action_unqualified_name
                                                    =
                                                    (uu___397_3311.FStar_Syntax_Syntax.action_unqualified_name);
                                                  FStar_Syntax_Syntax.action_univs
                                                    = us;
                                                  FStar_Syntax_Syntax.action_params
                                                    =
                                                    (uu___397_3311.FStar_Syntax_Syntax.action_params);
                                                  FStar_Syntax_Syntax.action_defn
                                                    = act_defn1;
                                                  FStar_Syntax_Syntax.action_typ
                                                    = uu____3312
                                                }
                                              else
                                                (let uu____3315 =
                                                   ((FStar_List.length us) =
                                                      (FStar_List.length
                                                         act1.FStar_Syntax_Syntax.action_univs))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1  ->
                                                           fun u2  ->
                                                             let uu____3322 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2
                                                                in
                                                             uu____3322 =
                                                               Prims.int_zero)
                                                        us
                                                        act1.FStar_Syntax_Syntax.action_univs)
                                                    in
                                                 if uu____3315
                                                 then
                                                   let uu___402_3327 = act1
                                                      in
                                                   let uu____3328 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                       act_typ2
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___402_3327.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___402_3327.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       =
                                                       (uu___402_3327.FStar_Syntax_Syntax.action_univs);
                                                     FStar_Syntax_Syntax.action_params
                                                       =
                                                       (uu___402_3327.FStar_Syntax_Syntax.action_params);
                                                     FStar_Syntax_Syntax.action_defn
                                                       = act_defn1;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____3328
                                                   }
                                                 else
                                                   (let uu____3331 =
                                                      let uu____3337 =
                                                        let uu____3339 =
                                                          FStar_Syntax_Print.univ_names_to_string
                                                            us
                                                           in
                                                        let uu____3341 =
                                                          FStar_Syntax_Print.univ_names_to_string
                                                            act1.FStar_Syntax_Syntax.action_univs
                                                           in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                          (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                          uu____3339
                                                          uu____3341
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____3337)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3331 r))
                                           in
                                        act2)))))))))
                in
             let fst1 uu____3364 =
               match uu____3364 with | (a,uu____3380,uu____3381) -> a  in
             let snd1 uu____3413 =
               match uu____3413 with | (uu____3428,b,uu____3430) -> b  in
             let thd uu____3462 =
               match uu____3462 with | (uu____3477,uu____3478,c) -> c  in
             let uu___420_3492 = ed  in
             let uu____3493 =
               FStar_All.pipe_right
                 ((fst1 stronger_repr), (snd1 stronger_repr))
                 (fun _3502  -> FStar_Pervasives_Native.Some _3502)
                in
             let uu____3503 =
               FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
                in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___420_3492.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___420_3492.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___420_3492.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs =
                 (uu___420_3492.FStar_Syntax_Syntax.univs);
               FStar_Syntax_Syntax.binders =
                 (uu___420_3492.FStar_Syntax_Syntax.binders);
               FStar_Syntax_Syntax.signature =
                 ((fst1 signature), (snd1 signature));
               FStar_Syntax_Syntax.ret_wp =
                 ((fst1 return_repr), (thd return_repr));
               FStar_Syntax_Syntax.bind_wp =
                 ((fst1 bind_repr), (thd bind_repr));
               FStar_Syntax_Syntax.stronger =
                 ((fst1 stronger_repr), (thd stronger_repr));
               FStar_Syntax_Syntax.match_wps =
                 (FStar_Util.Inr
                    {
                      FStar_Syntax_Syntax.conjunction =
                        ((fst1 conjunction), (snd1 conjunction))
                    });
               FStar_Syntax_Syntax.trivial =
                 (uu___420_3492.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
               FStar_Syntax_Syntax.return_repr =
                 ((fst1 return_repr), (snd1 return_repr));
               FStar_Syntax_Syntax.bind_repr =
                 ((fst1 bind_repr), (snd1 bind_repr));
               FStar_Syntax_Syntax.stronger_repr = uu____3493;
               FStar_Syntax_Syntax.actions = uu____3503;
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___420_3492.FStar_Syntax_Syntax.eff_attrs)
             })))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3554 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____3554 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3581 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____3581
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____3594 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____3594
       then
         let uu____3599 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____3599
       else ());
      (let uu____3605 =
         let uu____3610 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3610 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____3634 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____3634  in
             let uu____3635 =
               let uu____3642 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____3642 bs  in
             (match uu____3635 with
              | (bs1,uu____3648,uu____3649) ->
                  let uu____3650 =
                    let tmp_t =
                      let uu____3660 =
                        let uu____3663 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _3668  -> FStar_Pervasives_Native.Some _3668)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____3663
                         in
                      FStar_Syntax_Util.arrow bs1 uu____3660  in
                    let uu____3669 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____3669 with
                    | (us,tmp_t1) ->
                        let uu____3686 =
                          let uu____3687 =
                            let uu____3688 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____3688
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____3687
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____3686)
                     in
                  (match uu____3650 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____3757 ->
                            let uu____3760 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____3767 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____3767 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____3760
                            then (us, bs2)
                            else
                              (let uu____3778 =
                                 let uu____3784 =
                                   let uu____3786 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____3788 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____3786 uu____3788
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____3784)
                                  in
                               let uu____3792 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____3778 uu____3792))))
          in
       match uu____3605 with
       | (us,bs) ->
           let ed1 =
             let uu___460_3800 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___460_3800.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___460_3800.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___460_3800.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___460_3800.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___460_3800.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___460_3800.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___460_3800.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___460_3800.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___460_3800.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___460_3800.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___460_3800.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___460_3800.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___460_3800.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___460_3800.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___460_3800.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____3801 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____3801 with
            | (ed_univs_subst,ed_univs) ->
                let uu____3820 =
                  let uu____3825 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____3825  in
                (match uu____3820 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____3846 =
                         match uu____3846 with
                         | (us1,t) ->
                             let t1 =
                               let uu____3866 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3866 t  in
                             let uu____3875 =
                               let uu____3876 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3876 t1  in
                             (us1, uu____3875)
                          in
                       let uu___474_3881 = ed1  in
                       let uu____3882 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____3883 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____3884 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____3885 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____3886 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____3891 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____3894 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____3895 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____3896 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____3897 =
                         FStar_List.map
                           (fun a  ->
                              let uu___477_3905 = a  in
                              let uu____3906 =
                                let uu____3907 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____3907  in
                              let uu____3918 =
                                let uu____3919 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____3919  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___477_3905.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___477_3905.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___477_3905.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___477_3905.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____3906;
                                FStar_Syntax_Syntax.action_typ = uu____3918
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___474_3881.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___474_3881.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___474_3881.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___474_3881.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___474_3881.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____3882;
                         FStar_Syntax_Syntax.ret_wp = uu____3883;
                         FStar_Syntax_Syntax.bind_wp = uu____3884;
                         FStar_Syntax_Syntax.stronger = uu____3885;
                         FStar_Syntax_Syntax.match_wps = uu____3886;
                         FStar_Syntax_Syntax.trivial = uu____3891;
                         FStar_Syntax_Syntax.repr = uu____3894;
                         FStar_Syntax_Syntax.return_repr = uu____3895;
                         FStar_Syntax_Syntax.bind_repr = uu____3896;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____3897;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___474_3881.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____3931 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____3931
                       then
                         let uu____3936 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____3936
                       else ());
                      (let env =
                         let uu____3943 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____3943 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____3978 k =
                         match uu____3978 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____3998 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____3998 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4007 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4007 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4008 =
                                          let uu____4015 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4015 t1
                                           in
                                        (match uu____4008 with
                                         | (t2,uu____4017,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4020 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4020 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4036 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4038 =
                                               let uu____4040 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4040
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4036 uu____4038
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4055 ->
                                             let uu____4056 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4063 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4063 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4056
                                             then (g_us, t3)
                                             else
                                               (let uu____4074 =
                                                  let uu____4080 =
                                                    let uu____4082 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4084 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4082
                                                      uu____4084
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4080)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4074
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4092 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4092
                        then
                          let uu____4097 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4097
                        else ());
                       (let fresh_a_and_wp uu____4113 =
                          let fail1 t =
                            let uu____4126 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4126
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4142 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4142 with
                          | (uu____4153,signature1) ->
                              let uu____4155 =
                                let uu____4156 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4156.FStar_Syntax_Syntax.n  in
                              (match uu____4155 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4166) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4195)::(wp,uu____4197)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4226 -> fail1 signature1)
                               | uu____4227 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4241 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4241
                          then
                            let uu____4246 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4246
                          else ()  in
                        let ret_wp =
                          let uu____4252 = fresh_a_and_wp ()  in
                          match uu____4252 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4268 =
                                  let uu____4277 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4284 =
                                    let uu____4293 =
                                      let uu____4300 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4300
                                       in
                                    [uu____4293]  in
                                  uu____4277 :: uu____4284  in
                                let uu____4319 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4268 uu____4319
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4327 = fresh_a_and_wp ()  in
                           match uu____4327 with
                           | (a,wp_sort_a) ->
                               let uu____4340 = fresh_a_and_wp ()  in
                               (match uu____4340 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4356 =
                                        let uu____4365 =
                                          let uu____4372 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4372
                                           in
                                        [uu____4365]  in
                                      let uu____4385 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4356
                                        uu____4385
                                       in
                                    let k =
                                      let uu____4391 =
                                        let uu____4400 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4407 =
                                          let uu____4416 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4423 =
                                            let uu____4432 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4439 =
                                              let uu____4448 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4455 =
                                                let uu____4464 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4464]  in
                                              uu____4448 :: uu____4455  in
                                            uu____4432 :: uu____4439  in
                                          uu____4416 :: uu____4423  in
                                        uu____4400 :: uu____4407  in
                                      let uu____4507 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4391
                                        uu____4507
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4515 = fresh_a_and_wp ()  in
                            match uu____4515 with
                            | (a,wp_sort_a) ->
                                let uu____4528 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4528 with
                                 | (t,uu____4534) ->
                                     let k =
                                       let uu____4538 =
                                         let uu____4547 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4554 =
                                           let uu____4563 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____4570 =
                                             let uu____4579 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____4579]  in
                                           uu____4563 :: uu____4570  in
                                         uu____4547 :: uu____4554  in
                                       let uu____4610 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4538
                                         uu____4610
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____4622 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____4622 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____4637 = fresh_a_and_wp ()  in
                                   match uu____4637 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____4651 =
                                           let uu____4654 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____4654
                                            in
                                         let uu____4655 =
                                           let uu____4656 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____4656
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____4651 uu____4655
                                          in
                                       let k =
                                         let uu____4668 =
                                           let uu____4677 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____4684 =
                                             let uu____4693 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____4700 =
                                               let uu____4709 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____4716 =
                                                 let uu____4725 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____4725]  in
                                               uu____4709 :: uu____4716  in
                                             uu____4693 :: uu____4700  in
                                           uu____4677 :: uu____4684  in
                                         let uu____4762 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____4668
                                           uu____4762
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____4770 = fresh_a_and_wp ()  in
                                     match uu____4770 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____4786 =
                                             let uu____4795 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4802 =
                                               let uu____4811 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____4811]  in
                                             uu____4795 :: uu____4802  in
                                           let uu____4836 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____4786
                                             uu____4836
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____4844 = fresh_a_and_wp ()  in
                                      match uu____4844 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____4858 =
                                              let uu____4861 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____4861
                                               in
                                            let uu____4862 =
                                              let uu____4863 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____4863
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____4858 uu____4862
                                             in
                                          let wp_sort_b_a =
                                            let uu____4875 =
                                              let uu____4884 =
                                                let uu____4891 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4891
                                                 in
                                              [uu____4884]  in
                                            let uu____4904 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4875 uu____4904
                                             in
                                          let k =
                                            let uu____4910 =
                                              let uu____4919 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4926 =
                                                let uu____4935 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____4942 =
                                                  let uu____4951 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____4951]  in
                                                uu____4935 :: uu____4942  in
                                              uu____4919 :: uu____4926  in
                                            let uu____4982 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4910 uu____4982
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
                             let uu____4992 = fresh_a_and_wp ()  in
                             match uu____4992 with
                             | (a,wp_sort_a) ->
                                 let uu____5007 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5007 with
                                  | (t,uu____5015) ->
                                      let k =
                                        let uu____5019 =
                                          let uu____5028 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5035 =
                                            let uu____5044 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5044]  in
                                          uu____5028 :: uu____5035  in
                                        let uu____5069 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5019
                                          uu____5069
                                         in
                                      let trivial =
                                        let uu____5073 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5073
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5088 =
                             let uu____5099 =
                               let uu____5100 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5100.FStar_Syntax_Syntax.n  in
                             match uu____5099 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5119 ->
                                 let repr =
                                   let uu____5121 = fresh_a_and_wp ()  in
                                   match uu____5121 with
                                   | (a,wp_sort_a) ->
                                       let uu____5134 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5134 with
                                        | (t,uu____5140) ->
                                            let k =
                                              let uu____5144 =
                                                let uu____5153 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5160 =
                                                  let uu____5169 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5169]  in
                                                uu____5153 :: uu____5160  in
                                              let uu____5194 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5144 uu____5194
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5214 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5214 with
                                     | (uu____5221,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5224 =
                                           let uu____5231 =
                                             let uu____5232 =
                                               let uu____5249 =
                                                 let uu____5260 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5277 =
                                                   let uu____5288 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5288]  in
                                                 uu____5260 :: uu____5277  in
                                               (repr2, uu____5249)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5232
                                              in
                                           FStar_Syntax_Syntax.mk uu____5231
                                            in
                                         uu____5224
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5354 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5354 wp  in
                                   let destruct_repr t =
                                     let uu____5369 =
                                       let uu____5370 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5370.FStar_Syntax_Syntax.n  in
                                     match uu____5369 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5381,(t1,uu____5383)::
                                          (wp,uu____5385)::[])
                                         -> (t1, wp)
                                     | uu____5444 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5455 = fresh_a_and_wp ()  in
                                     match uu____5455 with
                                     | (a,uu____5463) ->
                                         let x_a =
                                           let uu____5469 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5469
                                            in
                                         let res =
                                           let wp =
                                             let uu____5477 =
                                               let uu____5482 =
                                                 let uu____5483 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5483
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5492 =
                                                 let uu____5493 =
                                                   let uu____5502 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5502
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5511 =
                                                   let uu____5522 =
                                                     let uu____5531 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5531
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5522]  in
                                                 uu____5493 :: uu____5511  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5482 uu____5492
                                                in
                                             uu____5477
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____5567 =
                                             let uu____5576 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5583 =
                                               let uu____5592 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____5592]  in
                                             uu____5576 :: uu____5583  in
                                           let uu____5617 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____5567
                                             uu____5617
                                            in
                                         let uu____5620 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____5620 with
                                          | (k1,uu____5628,uu____5629) ->
                                              let env1 =
                                                let uu____5633 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5633
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
                                        let uu____5644 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____5644
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____5645 = fresh_a_and_wp ()  in
                                      match uu____5645 with
                                      | (a,wp_sort_a) ->
                                          let uu____5658 = fresh_a_and_wp ()
                                             in
                                          (match uu____5658 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____5674 =
                                                   let uu____5683 =
                                                     let uu____5690 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5690
                                                      in
                                                   [uu____5683]  in
                                                 let uu____5703 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5674 uu____5703
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
                                                 let uu____5711 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____5711
                                                  in
                                               let wp_g_x =
                                                 let uu____5716 =
                                                   let uu____5721 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____5722 =
                                                     let uu____5723 =
                                                       let uu____5732 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5732
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5723]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____5721 uu____5722
                                                    in
                                                 uu____5716
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____5763 =
                                                     let uu____5768 =
                                                       let uu____5769 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5769
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____5778 =
                                                       let uu____5779 =
                                                         let uu____5782 =
                                                           let uu____5785 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____5786 =
                                                             let uu____5789 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____5790 =
                                                               let uu____5793
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____5794
                                                                 =
                                                                 let uu____5797
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____5797]
                                                                  in
                                                               uu____5793 ::
                                                                 uu____5794
                                                                in
                                                             uu____5789 ::
                                                               uu____5790
                                                              in
                                                           uu____5785 ::
                                                             uu____5786
                                                            in
                                                         r :: uu____5782  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____5779
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5768 uu____5778
                                                      in
                                                   uu____5763
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____5815 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____5815
                                                 then
                                                   let uu____5826 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____5833 =
                                                     let uu____5842 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____5842]  in
                                                   uu____5826 :: uu____5833
                                                 else []  in
                                               let k =
                                                 let uu____5878 =
                                                   let uu____5887 =
                                                     let uu____5896 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____5903 =
                                                       let uu____5912 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____5912]  in
                                                     uu____5896 :: uu____5903
                                                      in
                                                   let uu____5937 =
                                                     let uu____5946 =
                                                       let uu____5955 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____5962 =
                                                         let uu____5971 =
                                                           let uu____5978 =
                                                             let uu____5979 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____5979
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____5978
                                                            in
                                                         let uu____5980 =
                                                           let uu____5989 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____5996 =
                                                             let uu____6005 =
                                                               let uu____6012
                                                                 =
                                                                 let uu____6013
                                                                   =
                                                                   let uu____6022
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6022]
                                                                    in
                                                                 let uu____6041
                                                                   =
                                                                   let uu____6044
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6044
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6013
                                                                   uu____6041
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6012
                                                                in
                                                             [uu____6005]  in
                                                           uu____5989 ::
                                                             uu____5996
                                                            in
                                                         uu____5971 ::
                                                           uu____5980
                                                          in
                                                       uu____5955 ::
                                                         uu____5962
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____5946
                                                      in
                                                   FStar_List.append
                                                     uu____5887 uu____5937
                                                    in
                                                 let uu____6089 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5878 uu____6089
                                                  in
                                               let uu____6092 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6092 with
                                                | (k1,uu____6100,uu____6101)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___675_6113 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.strict_args_tab);
                                                           FStar_TypeChecker_Env.erasable_types_tab
                                                             =
                                                             (uu___675_6113.FStar_TypeChecker_Env.erasable_types_tab)
                                                         })
                                                        (fun _6115  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6115)
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
                                         (let uu____6142 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6156 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6156 with
                                               | (usubst,uvs) ->
                                                   let uu____6179 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6180 =
                                                     let uu___688_6181 = act
                                                        in
                                                     let uu____6182 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6183 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___688_6181.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___688_6181.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___688_6181.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6182;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6183
                                                     }  in
                                                   (uu____6179, uu____6180))
                                             in
                                          match uu____6142 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6187 =
                                                  let uu____6188 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6188.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6187 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6214 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6214
                                                    then
                                                      let uu____6217 =
                                                        let uu____6220 =
                                                          let uu____6221 =
                                                            let uu____6222 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6222
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6221
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6220
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6217
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6245 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6246 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6246 with
                                               | (act_typ1,uu____6254,g_t) ->
                                                   let env' =
                                                     let uu___705_6257 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.strict_args_tab);
                                                       FStar_TypeChecker_Env.erasable_types_tab
                                                         =
                                                         (uu___705_6257.FStar_TypeChecker_Env.erasable_types_tab)
                                                     }  in
                                                   ((let uu____6260 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6260
                                                     then
                                                       let uu____6264 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6266 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6268 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6264
                                                         uu____6266
                                                         uu____6268
                                                     else ());
                                                    (let uu____6273 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6273 with
                                                     | (act_defn,uu____6281,g_a)
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
                                                         let uu____6285 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6321
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6321
                                                                with
                                                                | (bs2,uu____6333)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6340
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6340
                                                                     in
                                                                    let uu____6343
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6343
                                                                    with
                                                                    | 
                                                                    (k1,uu____6357,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6361 ->
                                                               let uu____6362
                                                                 =
                                                                 let uu____6368
                                                                   =
                                                                   let uu____6370
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6372
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6370
                                                                    uu____6372
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6368)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6362
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6285
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6390
                                                                  =
                                                                  let uu____6391
                                                                    =
                                                                    let uu____6392
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6392
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6391
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6390);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6394
                                                                    =
                                                                    let uu____6395
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6395.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6394
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6420
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6420
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6427
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6427
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6447
                                                                    =
                                                                    let uu____6448
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6448]
                                                                     in
                                                                    let uu____6449
                                                                    =
                                                                    let uu____6460
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6460]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6447;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6449;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6485
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6485))
                                                                  | uu____6488
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6490
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
                                                                    let uu____6512
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6512))
                                                                   in
                                                                match uu____6490
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
                                                                    let uu___755_6531
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___755_6531.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___755_6531.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___755_6531.FStar_Syntax_Syntax.action_params);
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
                           match uu____5088 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6556 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6556
                                   ts1
                                  in
                               let ed3 =
                                 let uu___767_6566 = ed2  in
                                 let uu____6567 = cl signature  in
                                 let uu____6568 = cl ret_wp  in
                                 let uu____6569 = cl bind_wp  in
                                 let uu____6570 = cl stronger  in
                                 let uu____6571 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____6576 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____6579 = cl repr  in
                                 let uu____6580 = cl return_repr  in
                                 let uu____6581 = cl bind_repr  in
                                 let uu____6582 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___770_6590 = a  in
                                        let uu____6591 =
                                          let uu____6592 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____6592
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____6617 =
                                          let uu____6618 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____6618
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___770_6590.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___770_6590.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___770_6590.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___770_6590.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____6591;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____6617
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___767_6566.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___767_6566.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___767_6566.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___767_6566.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___767_6566.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____6567;
                                   FStar_Syntax_Syntax.ret_wp = uu____6568;
                                   FStar_Syntax_Syntax.bind_wp = uu____6569;
                                   FStar_Syntax_Syntax.stronger = uu____6570;
                                   FStar_Syntax_Syntax.match_wps = uu____6571;
                                   FStar_Syntax_Syntax.trivial = uu____6576;
                                   FStar_Syntax_Syntax.repr = uu____6579;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____6580;
                                   FStar_Syntax_Syntax.bind_repr = uu____6581;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____6582;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___767_6566.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____6644 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6644
                                 then
                                   let uu____6649 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____6649
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
        let fail1 uu____6702 =
          let uu____6703 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____6709 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____6703 uu____6709  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____6753)::(wp,uu____6755)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____6784 -> fail1 ())
        | uu____6785 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____6798 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____6798
       then
         let uu____6803 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____6803
       else ());
      (let uu____6808 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____6808 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           let uu____6854 =
             if (FStar_List.length us) = Prims.int_zero
             then (env0, us, lift)
             else
               (let uu____6878 = FStar_Syntax_Subst.open_univ_vars us lift
                   in
                match uu____6878 with
                | (us1,lift1) ->
                    let uu____6893 =
                      FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                    (uu____6893, us1, lift1))
              in
           (match uu____6854 with
            | (env,us1,lift1) ->
                let uu____6903 =
                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                (match uu____6903 with
                 | (lift2,lc,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let lift_ty =
                         FStar_All.pipe_right
                           lc.FStar_TypeChecker_Common.res_typ
                           (FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env0)
                          in
                       (let uu____6916 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "LayeredEffects")
                           in
                        if uu____6916
                        then
                          let uu____6921 =
                            FStar_Syntax_Print.term_to_string lift2  in
                          let uu____6923 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.print2
                            "Typechecked lift: %s and lift_ty: %s\n"
                            uu____6921 uu____6923
                        else ());
                       (let lift_t_shape_error s =
                          let uu____6937 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.source
                             in
                          let uu____6939 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.target
                             in
                          let uu____6941 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.format4
                            "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                            uu____6937 uu____6939 s uu____6941
                           in
                        let uu____6944 =
                          let uu____6951 =
                            let uu____6956 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____6956
                              (fun uu____6973  ->
                                 match uu____6973 with
                                 | (t,u) ->
                                     let uu____6984 =
                                       let uu____6985 =
                                         FStar_Syntax_Syntax.gen_bv "a"
                                           FStar_Pervasives_Native.None t
                                          in
                                       FStar_All.pipe_right uu____6985
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____6984, u))
                             in
                          match uu____6951 with
                          | (a,u_a) ->
                              let rest_bs =
                                let uu____7004 =
                                  let uu____7005 =
                                    FStar_Syntax_Subst.compress lift_ty  in
                                  uu____7005.FStar_Syntax_Syntax.n  in
                                match uu____7004 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs,uu____7017) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____7045 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match uu____7045 with
                                     | (a',uu____7055)::bs1 ->
                                         let uu____7075 =
                                           let uu____7076 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     Prims.int_one))
                                              in
                                           FStar_All.pipe_right uu____7076
                                             FStar_Pervasives_Native.fst
                                            in
                                         let uu____7174 =
                                           let uu____7187 =
                                             let uu____7190 =
                                               let uu____7191 =
                                                 let uu____7198 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a)
                                                    in
                                                 (a', uu____7198)  in
                                               FStar_Syntax_Syntax.NT
                                                 uu____7191
                                                in
                                             [uu____7190]  in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____7187
                                            in
                                         FStar_All.pipe_right uu____7075
                                           uu____7174)
                                | uu____7213 ->
                                    let uu____7214 =
                                      let uu____7220 =
                                        lift_t_shape_error
                                          "either not an arrow, or not enough binders"
                                         in
                                      (FStar_Errors.Fatal_UnexpectedExpressionType,
                                        uu____7220)
                                       in
                                    FStar_Errors.raise_error uu____7214 r
                                 in
                              let uu____7232 =
                                let uu____7243 =
                                  let uu____7248 =
                                    FStar_TypeChecker_Env.push_binders env (a
                                      :: rest_bs)
                                     in
                                  let uu____7255 =
                                    let uu____7256 =
                                      FStar_All.pipe_right a
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_All.pipe_right uu____7256
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  FStar_TypeChecker_Util.fresh_effect_repr_en
                                    uu____7248 r
                                    sub1.FStar_Syntax_Syntax.source u_a
                                    uu____7255
                                   in
                                match uu____7243 with
                                | (f_sort,g1) ->
                                    let uu____7277 =
                                      let uu____7284 =
                                        FStar_Syntax_Syntax.gen_bv "f"
                                          FStar_Pervasives_Native.None f_sort
                                         in
                                      FStar_All.pipe_right uu____7284
                                        FStar_Syntax_Syntax.mk_binder
                                       in
                                    (uu____7277, g1)
                                 in
                              (match uu____7232 with
                               | (f_b,g_f_b) ->
                                   let bs = a ::
                                     (FStar_List.append rest_bs [f_b])  in
                                   let uu____7351 =
                                     let uu____7356 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____7357 =
                                       let uu____7358 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7358
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_effect_repr_en
                                       uu____7356 r
                                       sub1.FStar_Syntax_Syntax.target u_a
                                       uu____7357
                                      in
                                   (match uu____7351 with
                                    | (repr,g_repr) ->
                                        let uu____7375 =
                                          let uu____7378 =
                                            let uu____7381 =
                                              let uu____7384 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              FStar_All.pipe_right uu____7384
                                                (fun _7387  ->
                                                   FStar_Pervasives_Native.Some
                                                     _7387)
                                               in
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr uu____7381
                                             in
                                          FStar_Syntax_Util.arrow bs
                                            uu____7378
                                           in
                                        let uu____7388 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_f_b g_repr
                                           in
                                        (uu____7375, uu____7388)))
                           in
                        match uu____6944 with
                        | (k,g_k) ->
                            ((let uu____7398 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____7398
                              then
                                let uu____7403 =
                                  FStar_Syntax_Print.term_to_string k  in
                                FStar_Util.print1
                                  "tc_layered_lift: before unification k: %s\n"
                                  uu____7403
                              else ());
                             (let g1 =
                                FStar_TypeChecker_Rel.teq env lift_ty k  in
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g_k;
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g1;
                              (let uu____7412 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env0)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____7412
                               then
                                 let uu____7417 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "After unification k: %s\n" uu____7417
                               else ());
                              (let uu____7422 =
                                 let uu____7435 =
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 lift2
                                    in
                                 match uu____7435 with
                                 | (inst_us,lift3) ->
                                     (if
                                        (FStar_List.length inst_us) <>
                                          Prims.int_one
                                      then
                                        (let uu____7462 =
                                           let uu____7468 =
                                             let uu____7470 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.source
                                                in
                                             let uu____7472 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.target
                                                in
                                             let uu____7474 =
                                               let uu____7476 =
                                                 FStar_All.pipe_right inst_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7476
                                                 FStar_Util.string_of_int
                                                in
                                             let uu____7483 =
                                               FStar_Syntax_Print.term_to_string
                                                 lift3
                                                in
                                             FStar_Util.format4
                                               "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                               uu____7470 uu____7472
                                               uu____7474 uu____7483
                                              in
                                           (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                             uu____7468)
                                            in
                                         FStar_Errors.raise_error uu____7462
                                           r)
                                      else ();
                                      (let uu____7489 =
                                         ((FStar_List.length us1) =
                                            Prims.int_zero)
                                           ||
                                           (((FStar_List.length us1) =
                                               (FStar_List.length inst_us))
                                              &&
                                              (FStar_List.forall2
                                                 (fun u1  ->
                                                    fun u2  ->
                                                      let uu____7498 =
                                                        FStar_Syntax_Syntax.order_univ_name
                                                          u1 u2
                                                         in
                                                      uu____7498 =
                                                        Prims.int_zero) us1
                                                 inst_us))
                                          in
                                       if uu____7489
                                       then
                                         let uu____7515 =
                                           let uu____7518 =
                                             FStar_All.pipe_right k
                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____7518
                                             (FStar_Syntax_Subst.close_univ_vars
                                                inst_us)
                                            in
                                         (inst_us, lift3, uu____7515)
                                       else
                                         (let uu____7529 =
                                            let uu____7535 =
                                              let uu____7537 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____7539 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____7541 =
                                                let uu____7543 =
                                                  FStar_All.pipe_right us1
                                                    FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7543
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7550 =
                                                let uu____7552 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7552
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7559 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format5
                                                "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                uu____7537 uu____7539
                                                uu____7541 uu____7550
                                                uu____7559
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____7535)
                                             in
                                          FStar_Errors.raise_error uu____7529
                                            r)))
                                  in
                               match uu____7422 with
                               | (us2,lift3,lift_wp) ->
                                   let sub2 =
                                     let uu___873_7591 = sub1  in
                                     {
                                       FStar_Syntax_Syntax.source =
                                         (uu___873_7591.FStar_Syntax_Syntax.source);
                                       FStar_Syntax_Syntax.target =
                                         (uu___873_7591.FStar_Syntax_Syntax.target);
                                       FStar_Syntax_Syntax.lift_wp =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift_wp));
                                       FStar_Syntax_Syntax.lift =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift3))
                                     }  in
                                   ((let uu____7601 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env0)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____7601
                                     then
                                       let uu____7606 =
                                         FStar_Syntax_Print.sub_eff_to_string
                                           sub2
                                          in
                                       FStar_Util.print1
                                         "Final sub_effect: %s\n" uu____7606
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
          (let uu____7632 =
             let uu____7639 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____7639
              in
           match uu____7632 with
           | (a,wp_a_src) ->
               let uu____7646 =
                 let uu____7653 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7653
                  in
               (match uu____7646 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7661 =
                        let uu____7664 =
                          let uu____7665 =
                            let uu____7672 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7672)  in
                          FStar_Syntax_Syntax.NT uu____7665  in
                        [uu____7664]  in
                      FStar_Syntax_Subst.subst uu____7661 wp_b_tgt  in
                    let expected_k =
                      let uu____7680 =
                        let uu____7689 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7696 =
                          let uu____7705 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7705]  in
                        uu____7689 :: uu____7696  in
                      let uu____7730 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7680 uu____7730  in
                    let repr_type eff_name a1 wp =
                      (let uu____7752 =
                         let uu____7754 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____7754  in
                       if uu____7752
                       then
                         let uu____7757 =
                           let uu____7763 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____7763)
                            in
                         let uu____7767 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____7757 uu____7767
                       else ());
                      (let uu____7770 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____7770 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____7803 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____7804 =
                             let uu____7811 =
                               let uu____7812 =
                                 let uu____7829 =
                                   let uu____7840 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____7849 =
                                     let uu____7860 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____7860]  in
                                   uu____7840 :: uu____7849  in
                                 (repr, uu____7829)  in
                               FStar_Syntax_Syntax.Tm_app uu____7812  in
                             FStar_Syntax_Syntax.mk uu____7811  in
                           uu____7804 FStar_Pervasives_Native.None uu____7803)
                       in
                    let uu____7905 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____8078 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____8089 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____8089 with
                              | (usubst,uvs1) ->
                                  let uu____8112 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8113 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8112, uu____8113)
                            else (env, lift_wp)  in
                          (match uu____8078 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8163 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8163))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8234 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8249 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8249 with
                              | (usubst,uvs) ->
                                  let uu____8274 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8274)
                            else ([], lift)  in
                          (match uu____8234 with
                           | (uvs,lift1) ->
                               ((let uu____8310 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____8310
                                 then
                                   let uu____8314 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____8314
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____8320 =
                                   let uu____8327 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____8327 lift1
                                    in
                                 match uu____8320 with
                                 | (lift2,comp,uu____8352) ->
                                     let uu____8353 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8353 with
                                      | (uu____8382,lift_wp,lift_elab) ->
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
                                            let uu____8414 =
                                              let uu____8425 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8425
                                               in
                                            let uu____8442 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8414, uu____8442)
                                          else
                                            (let uu____8471 =
                                               let uu____8482 =
                                                 let uu____8491 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8491)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8482
                                                in
                                             let uu____8506 =
                                               let uu____8515 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8515)  in
                                             (uu____8471, uu____8506))))))
                       in
                    (match uu____7905 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___953_8579 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___953_8579.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___953_8579.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___953_8579.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___953_8579.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___953_8579.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___953_8579.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___953_8579.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___953_8579.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___953_8579.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___953_8579.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___953_8579.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___953_8579.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___953_8579.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___953_8579.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___953_8579.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___953_8579.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___953_8579.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___953_8579.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___953_8579.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___953_8579.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___953_8579.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___953_8579.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___953_8579.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___953_8579.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___953_8579.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___953_8579.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___953_8579.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___953_8579.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___953_8579.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___953_8579.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___953_8579.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___953_8579.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___953_8579.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___953_8579.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___953_8579.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___953_8579.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___953_8579.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___953_8579.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___953_8579.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___953_8579.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___953_8579.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___953_8579.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___953_8579.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___953_8579.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___953_8579.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8612 =
                                 let uu____8617 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8617 with
                                 | (usubst,uvs1) ->
                                     let uu____8640 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8641 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8640, uu____8641)
                                  in
                               (match uu____8612 with
                                | (env2,lift2) ->
                                    let uu____8646 =
                                      let uu____8653 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8653
                                       in
                                    (match uu____8646 with
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
                                             let uu____8679 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8680 =
                                               let uu____8687 =
                                                 let uu____8688 =
                                                   let uu____8705 =
                                                     let uu____8716 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8725 =
                                                       let uu____8736 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8736]  in
                                                     uu____8716 :: uu____8725
                                                      in
                                                   (lift_wp1, uu____8705)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8688
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8687
                                                in
                                             uu____8680
                                               FStar_Pervasives_Native.None
                                               uu____8679
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8784 =
                                             let uu____8793 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8800 =
                                               let uu____8809 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8816 =
                                                 let uu____8825 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8825]  in
                                               uu____8809 :: uu____8816  in
                                             uu____8793 :: uu____8800  in
                                           let uu____8856 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8784
                                             uu____8856
                                            in
                                         let uu____8859 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8859 with
                                          | (expected_k2,uu____8869,uu____8870)
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
                                                   let uu____8878 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8878))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8886 =
                             let uu____8888 =
                               let uu____8890 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8890
                                 FStar_List.length
                                in
                             uu____8888 <> Prims.int_one  in
                           if uu____8886
                           then
                             let uu____8913 =
                               let uu____8919 =
                                 let uu____8921 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8923 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8925 =
                                   let uu____8927 =
                                     let uu____8929 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8929
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8927
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8921 uu____8923 uu____8925
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8919)
                                in
                             FStar_Errors.raise_error uu____8913 r
                           else ());
                          (let uu____8956 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8959 =
                                  let uu____8961 =
                                    let uu____8964 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8964
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8961
                                    FStar_List.length
                                   in
                                uu____8959 <> Prims.int_one)
                              in
                           if uu____8956
                           then
                             let uu____9002 =
                               let uu____9008 =
                                 let uu____9010 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9012 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9014 =
                                   let uu____9016 =
                                     let uu____9018 =
                                       let uu____9021 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____9021
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9018
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9016
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9010 uu____9012 uu____9014
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9008)
                                in
                             FStar_Errors.raise_error uu____9002 r
                           else ());
                          (let uu___990_9063 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___990_9063.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___990_9063.FStar_Syntax_Syntax.target);
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
    fun uu____9094  ->
      fun r  ->
        match uu____9094 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9117 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9145 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9145 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9176 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9176 c  in
                     let uu____9185 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9185, uvs1, tps1, c1))
               in
            (match uu____9117 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9205 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9205 with
                  | (tps2,c2) ->
                      let uu____9220 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9220 with
                       | (tps3,env3,us) ->
                           let uu____9238 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____9238 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____9264)::uu____9265 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____9284 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____9292 =
                                    let uu____9294 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____9294  in
                                  if uu____9292
                                  then
                                    let uu____9297 =
                                      let uu____9303 =
                                        let uu____9305 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____9307 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____9305 uu____9307
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____9303)
                                       in
                                    FStar_Errors.raise_error uu____9297 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____9315 =
                                    let uu____9316 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____9316
                                     in
                                  match uu____9315 with
                                  | (uvs2,t) ->
                                      let uu____9345 =
                                        let uu____9350 =
                                          let uu____9363 =
                                            let uu____9364 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____9364.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____9363)  in
                                        match uu____9350 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____9379,c5)) -> ([], c5)
                                        | (uu____9421,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____9460 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____9345 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____9492 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____9492 with
                                               | (uu____9497,t1) ->
                                                   let uu____9499 =
                                                     let uu____9505 =
                                                       let uu____9507 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____9509 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____9513 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____9507
                                                         uu____9509
                                                         uu____9513
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____9505)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____9499 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  