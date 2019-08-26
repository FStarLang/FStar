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
                                        let reason =
                                          FStar_Util.format1
                                            "implicit for pure_wp in checking stronger for %s"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           in
                                        let uu____2346 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          reason r uu____2346 pure_wp_t
                                         in
                                      (match uu____2330 with
                                       | (pure_wp_uvar,uu____2360,guard_wp)
                                           ->
                                           let c =
                                             let uu____2375 =
                                               let uu____2376 =
                                                 let uu____2377 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2377]  in
                                               let uu____2378 =
                                                 let uu____2389 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2389]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2376;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2378;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2375
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2444 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2444
                                             then
                                               let uu____2449 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2449
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
                                              let uu____2457 =
                                                let uu____2460 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2460
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2457))))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let tc_action env act =
              let env01 = env  in
              let r =
                (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                 in
              if
                (FStar_List.length act.FStar_Syntax_Syntax.action_params) <>
                  Prims.int_zero
              then
                (let uu____2494 =
                   let uu____2500 =
                     let uu____2502 =
                       FStar_Syntax_Print.binders_to_string "; "
                         act.FStar_Syntax_Syntax.action_params
                        in
                     FStar_Util.format3
                       "Action %s:%s has non-empty action params (%s)"
                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                       (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                       uu____2502
                      in
                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                     uu____2500)
                    in
                 FStar_Errors.raise_error uu____2494 r)
              else ();
              (let uu____2509 =
                 let uu____2514 =
                   FStar_Syntax_Subst.univ_var_opening
                     act.FStar_Syntax_Syntax.action_univs
                    in
                 match uu____2514 with
                 | (usubst,us) ->
                     let uu____2537 =
                       FStar_TypeChecker_Env.push_univ_vars env us  in
                     let uu____2538 =
                       let uu___268_2539 = act  in
                       let uu____2540 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_defn
                          in
                       let uu____2541 =
                         FStar_Syntax_Subst.subst usubst
                           act.FStar_Syntax_Syntax.action_typ
                          in
                       {
                         FStar_Syntax_Syntax.action_name =
                           (uu___268_2539.FStar_Syntax_Syntax.action_name);
                         FStar_Syntax_Syntax.action_unqualified_name =
                           (uu___268_2539.FStar_Syntax_Syntax.action_unqualified_name);
                         FStar_Syntax_Syntax.action_univs = us;
                         FStar_Syntax_Syntax.action_params =
                           (uu___268_2539.FStar_Syntax_Syntax.action_params);
                         FStar_Syntax_Syntax.action_defn = uu____2540;
                         FStar_Syntax_Syntax.action_typ = uu____2541
                       }  in
                     (uu____2537, uu____2538)
                  in
               match uu____2509 with
               | (env1,act1) ->
                   let act_typ =
                     let uu____2545 =
                       let uu____2546 =
                         FStar_Syntax_Subst.compress
                           act1.FStar_Syntax_Syntax.action_typ
                          in
                       uu____2546.FStar_Syntax_Syntax.n  in
                     match uu____2545 with
                     | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                         let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                         let uu____2572 =
                           FStar_Ident.lid_equals
                             ct.FStar_Syntax_Syntax.effect_name
                             ed.FStar_Syntax_Syntax.mname
                            in
                         if uu____2572
                         then
                           let repr_ts =
                             let uu____2576 = repr  in
                             match uu____2576 with
                             | (us,t,uu____2591) -> (us, t)  in
                           let repr1 =
                             let uu____2609 =
                               FStar_TypeChecker_Env.inst_tscheme_with
                                 repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                in
                             FStar_All.pipe_right uu____2609
                               FStar_Pervasives_Native.snd
                              in
                           let repr2 =
                             let uu____2621 =
                               let uu____2626 =
                                 let uu____2627 =
                                   FStar_Syntax_Syntax.as_arg
                                     ct.FStar_Syntax_Syntax.result_typ
                                    in
                                 uu____2627 ::
                                   (ct.FStar_Syntax_Syntax.effect_args)
                                  in
                               FStar_Syntax_Syntax.mk_Tm_app repr1 uu____2626
                                in
                             uu____2621 FStar_Pervasives_Native.None r  in
                           let c1 =
                             let uu____2645 =
                               let uu____2648 =
                                 FStar_TypeChecker_Env.new_u_univ ()  in
                               FStar_Pervasives_Native.Some uu____2648  in
                             FStar_Syntax_Syntax.mk_Total' repr2 uu____2645
                              in
                           FStar_Syntax_Util.arrow bs c1
                         else act1.FStar_Syntax_Syntax.action_typ
                     | uu____2651 -> act1.FStar_Syntax_Syntax.action_typ  in
                   let uu____2652 =
                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                       act_typ
                      in
                   (match uu____2652 with
                    | (act_typ1,uu____2660,g_t) ->
                        let uu____2662 =
                          let uu____2669 =
                            let uu___293_2670 =
                              FStar_TypeChecker_Env.set_expected_typ env1
                                act_typ1
                               in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___293_2670.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___293_2670.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___293_2670.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___293_2670.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___293_2670.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___293_2670.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___293_2670.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___293_2670.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___293_2670.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___293_2670.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___293_2670.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp = false;
                              FStar_TypeChecker_Env.effects =
                                (uu___293_2670.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___293_2670.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___293_2670.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___293_2670.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___293_2670.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___293_2670.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___293_2670.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___293_2670.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax =
                                (uu___293_2670.FStar_TypeChecker_Env.lax);
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___293_2670.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___293_2670.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___293_2670.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___293_2670.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___293_2670.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___293_2670.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___293_2670.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___293_2670.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___293_2670.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___293_2670.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___293_2670.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___293_2670.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___293_2670.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___293_2670.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___293_2670.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___293_2670.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___293_2670.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___293_2670.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___293_2670.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___293_2670.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___293_2670.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___293_2670.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___293_2670.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___293_2670.FStar_TypeChecker_Env.strict_args_tab)
                            }  in
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                            uu____2669 act1.FStar_Syntax_Syntax.action_defn
                           in
                        (match uu____2662 with
                         | (act_defn,uu____2673,g_d) ->
                             ((let uu____2676 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env1)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____2676
                               then
                                 let uu____2681 =
                                   FStar_Syntax_Print.term_to_string act_defn
                                    in
                                 let uu____2683 =
                                   FStar_Syntax_Print.term_to_string act_typ1
                                    in
                                 FStar_Util.print2
                                   "Typechecked action definition: %s and action type: %s\n"
                                   uu____2681 uu____2683
                               else ());
                              (let uu____2688 =
                                 let act_typ2 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Beta] env1
                                     act_typ1
                                    in
                                 let uu____2696 =
                                   let uu____2697 =
                                     FStar_Syntax_Subst.compress act_typ2  in
                                   uu____2697.FStar_Syntax_Syntax.n  in
                                 match uu____2696 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____2707) ->
                                     let bs1 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     let env2 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs1
                                        in
                                     let uu____2730 =
                                       FStar_Syntax_Util.type_u ()  in
                                     (match uu____2730 with
                                      | (t,u) ->
                                          let reason =
                                            FStar_Util.format2
                                              "implicit for return type of action %s:%s"
                                              (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                              (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                             in
                                          let uu____2746 =
                                            FStar_TypeChecker_Util.new_implicit_var
                                              reason r env2 t
                                             in
                                          (match uu____2746 with
                                           | (a_tm,uu____2766,g_tm) ->
                                               let uu____2780 =
                                                 fresh_repr r env2 u a_tm  in
                                               (match uu____2780 with
                                                | (repr1,g) ->
                                                    let uu____2793 =
                                                      let uu____2796 =
                                                        let uu____2799 =
                                                          let uu____2802 =
                                                            FStar_TypeChecker_Env.new_u_univ
                                                              ()
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2802
                                                            (fun _2805  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _2805)
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total'
                                                          repr1 uu____2799
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____2796
                                                       in
                                                    let uu____2806 =
                                                      FStar_TypeChecker_Env.conj_guard
                                                        g g_tm
                                                       in
                                                    (uu____2793, uu____2806))))
                                 | uu____2809 ->
                                     let uu____2810 =
                                       let uu____2816 =
                                         let uu____2818 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.format3
                                           "Unexpected non-function type for action %s:%s (%s)"
                                           (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                           uu____2818
                                          in
                                       (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                         uu____2816)
                                        in
                                     FStar_Errors.raise_error uu____2810 r
                                  in
                               match uu____2688 with
                               | (k,g_k) ->
                                   ((let uu____2835 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____2835
                                     then
                                       let uu____2840 =
                                         FStar_Syntax_Print.term_to_string k
                                          in
                                       FStar_Util.print1
                                         "Expected action type: %s\n"
                                         uu____2840
                                     else ());
                                    (let g =
                                       FStar_TypeChecker_Rel.teq env1
                                         act_typ1 k
                                        in
                                     FStar_List.iter
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1) [g_t; g_d; g_k; g];
                                     (let uu____2848 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____2848
                                      then
                                        let uu____2853 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type after unification: %s\n"
                                          uu____2853
                                      else ());
                                     (let act_typ2 =
                                        let err_msg t =
                                          let uu____2866 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          FStar_Util.format3
                                            "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                            (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                            uu____2866
                                           in
                                        let repr_args t =
                                          let uu____2887 =
                                            let uu____2888 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____2888.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2887 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (head1,a::is) ->
                                              let uu____2940 =
                                                let uu____2941 =
                                                  FStar_Syntax_Subst.compress
                                                    head1
                                                   in
                                                uu____2941.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____2940 with
                                               | FStar_Syntax_Syntax.Tm_uinst
                                                   (uu____2950,us) ->
                                                   (us,
                                                     (FStar_Pervasives_Native.fst
                                                        a), is)
                                               | uu____2960 ->
                                                   let uu____2961 =
                                                     let uu____2967 =
                                                       err_msg t  in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____2967)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____2961 r)
                                          | uu____2976 ->
                                              let uu____2977 =
                                                let uu____2983 = err_msg t
                                                   in
                                                (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                  uu____2983)
                                                 in
                                              FStar_Errors.raise_error
                                                uu____2977 r
                                           in
                                        let k1 =
                                          FStar_TypeChecker_Normalize.normalize
                                            [FStar_TypeChecker_Env.Beta] env1
                                            k
                                           in
                                        let uu____2993 =
                                          let uu____2994 =
                                            FStar_Syntax_Subst.compress k1
                                             in
                                          uu____2994.FStar_Syntax_Syntax.n
                                           in
                                        match uu____2993 with
                                        | FStar_Syntax_Syntax.Tm_arrow 
                                            (bs,c) ->
                                            let uu____3019 =
                                              FStar_Syntax_Subst.open_comp bs
                                                c
                                               in
                                            (match uu____3019 with
                                             | (bs1,c1) ->
                                                 let uu____3026 =
                                                   repr_args
                                                     (FStar_Syntax_Util.comp_result
                                                        c1)
                                                    in
                                                 (match uu____3026 with
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
                                                      let uu____3037 =
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          ct
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____3037))
                                        | uu____3040 ->
                                            let uu____3041 =
                                              let uu____3047 = err_msg k1  in
                                              (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                uu____3047)
                                               in
                                            FStar_Errors.raise_error
                                              uu____3041 r
                                         in
                                      (let uu____3051 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3051
                                       then
                                         let uu____3056 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ2
                                            in
                                         FStar_Util.print1
                                           "Action type after injecting it into the monad: %s\n"
                                           uu____3056
                                       else ());
                                      (let act2 =
                                         let uu____3062 =
                                           FStar_TypeChecker_Util.generalize_universes
                                             env1 act_defn
                                            in
                                         match uu____3062 with
                                         | (us,act_defn1) ->
                                             if
                                               act1.FStar_Syntax_Syntax.action_univs
                                                 = []
                                             then
                                               let uu___366_3076 = act1  in
                                               let uu____3077 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   us act_typ2
                                                  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___366_3076.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___366_3076.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   = us;
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___366_3076.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = act_defn1;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____3077
                                               }
                                             else
                                               (let uu____3080 =
                                                  ((FStar_List.length us) =
                                                     (FStar_List.length
                                                        act1.FStar_Syntax_Syntax.action_univs))
                                                    &&
                                                    (FStar_List.forall2
                                                       (fun u1  ->
                                                          fun u2  ->
                                                            let uu____3087 =
                                                              FStar_Syntax_Syntax.order_univ_name
                                                                u1 u2
                                                               in
                                                            uu____3087 =
                                                              Prims.int_zero)
                                                       us
                                                       act1.FStar_Syntax_Syntax.action_univs)
                                                   in
                                                if uu____3080
                                                then
                                                  let uu___371_3092 = act1
                                                     in
                                                  let uu____3093 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      act1.FStar_Syntax_Syntax.action_univs
                                                      act_typ2
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___371_3092.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___371_3092.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      =
                                                      (uu___371_3092.FStar_Syntax_Syntax.action_univs);
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___371_3092.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____3093
                                                  }
                                                else
                                                  (let uu____3096 =
                                                     let uu____3102 =
                                                       let uu____3104 =
                                                         FStar_Syntax_Print.univ_names_to_string
                                                           us
                                                          in
                                                       let uu____3106 =
                                                         FStar_Syntax_Print.univ_names_to_string
                                                           act1.FStar_Syntax_Syntax.action_univs
                                                          in
                                                       FStar_Util.format4
                                                         "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                         (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                         (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                         uu____3104
                                                         uu____3106
                                                        in
                                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                       uu____3102)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____3096 r))
                                          in
                                       act2)))))))))
               in
            let fst1 uu____3129 =
              match uu____3129 with | (a,uu____3145,uu____3146) -> a  in
            let snd1 uu____3178 =
              match uu____3178 with | (uu____3193,b,uu____3195) -> b  in
            let thd uu____3227 =
              match uu____3227 with | (uu____3242,uu____3243,c) -> c  in
            let uu___389_3257 = ed  in
            let uu____3258 =
              FStar_All.pipe_right
                ((fst1 stronger_repr), (snd1 stronger_repr))
                (fun _3267  -> FStar_Pervasives_Native.Some _3267)
               in
            let uu____3268 =
              FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
               in
            {
              FStar_Syntax_Syntax.is_layered =
                (uu___389_3257.FStar_Syntax_Syntax.is_layered);
              FStar_Syntax_Syntax.cattributes =
                (uu___389_3257.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.mname =
                (uu___389_3257.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.univs =
                (uu___389_3257.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders =
                (uu___389_3257.FStar_Syntax_Syntax.binders);
              FStar_Syntax_Syntax.signature =
                ((fst1 signature), (snd1 signature));
              FStar_Syntax_Syntax.ret_wp =
                ((fst1 return_repr), (thd return_repr));
              FStar_Syntax_Syntax.bind_wp =
                ((fst1 bind_repr), (thd bind_repr));
              FStar_Syntax_Syntax.stronger =
                ((fst1 stronger_repr), (thd stronger_repr));
              FStar_Syntax_Syntax.match_wps =
                (uu___389_3257.FStar_Syntax_Syntax.match_wps);
              FStar_Syntax_Syntax.trivial =
                (uu___389_3257.FStar_Syntax_Syntax.trivial);
              FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
              FStar_Syntax_Syntax.return_repr =
                ((fst1 return_repr), (snd1 return_repr));
              FStar_Syntax_Syntax.bind_repr =
                ((fst1 bind_repr), (snd1 bind_repr));
              FStar_Syntax_Syntax.stronger_repr = uu____3258;
              FStar_Syntax_Syntax.actions = uu____3268;
              FStar_Syntax_Syntax.eff_attrs =
                (uu___389_3257.FStar_Syntax_Syntax.eff_attrs)
            }))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3315 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____3315 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3342 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____3342
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____3355 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____3355
       then
         let uu____3360 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____3360
       else ());
      (let uu____3366 =
         let uu____3371 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____3371 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____3395 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____3395  in
             let uu____3396 =
               let uu____3403 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____3403 bs  in
             (match uu____3396 with
              | (bs1,uu____3409,uu____3410) ->
                  let uu____3411 =
                    let tmp_t =
                      let uu____3421 =
                        let uu____3424 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _3429  -> FStar_Pervasives_Native.Some _3429)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____3424
                         in
                      FStar_Syntax_Util.arrow bs1 uu____3421  in
                    let uu____3430 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____3430 with
                    | (us,tmp_t1) ->
                        let uu____3447 =
                          let uu____3448 =
                            let uu____3449 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____3449
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____3448
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____3447)
                     in
                  (match uu____3411 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____3518 ->
                            let uu____3521 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____3528 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____3528 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____3521
                            then (us, bs2)
                            else
                              (let uu____3539 =
                                 let uu____3545 =
                                   let uu____3547 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____3549 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____3547 uu____3549
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____3545)
                                  in
                               let uu____3553 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____3539 uu____3553))))
          in
       match uu____3366 with
       | (us,bs) ->
           let ed1 =
             let uu___429_3561 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___429_3561.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___429_3561.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___429_3561.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___429_3561.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___429_3561.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___429_3561.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___429_3561.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___429_3561.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___429_3561.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___429_3561.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___429_3561.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___429_3561.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___429_3561.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___429_3561.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___429_3561.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____3562 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____3562 with
            | (ed_univs_subst,ed_univs) ->
                let uu____3581 =
                  let uu____3586 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____3586  in
                (match uu____3581 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____3607 =
                         match uu____3607 with
                         | (us1,t) ->
                             let t1 =
                               let uu____3627 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3627 t  in
                             let uu____3636 =
                               let uu____3637 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____3637 t1  in
                             (us1, uu____3636)
                          in
                       let uu___443_3642 = ed1  in
                       let uu____3643 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____3644 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____3645 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____3646 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____3647 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____3652 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____3655 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____3656 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____3657 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____3658 =
                         FStar_List.map
                           (fun a  ->
                              let uu___446_3666 = a  in
                              let uu____3667 =
                                let uu____3668 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____3668  in
                              let uu____3679 =
                                let uu____3680 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____3680  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___446_3666.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___446_3666.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___446_3666.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___446_3666.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____3667;
                                FStar_Syntax_Syntax.action_typ = uu____3679
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___443_3642.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___443_3642.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___443_3642.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___443_3642.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___443_3642.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____3643;
                         FStar_Syntax_Syntax.ret_wp = uu____3644;
                         FStar_Syntax_Syntax.bind_wp = uu____3645;
                         FStar_Syntax_Syntax.stronger = uu____3646;
                         FStar_Syntax_Syntax.match_wps = uu____3647;
                         FStar_Syntax_Syntax.trivial = uu____3652;
                         FStar_Syntax_Syntax.repr = uu____3655;
                         FStar_Syntax_Syntax.return_repr = uu____3656;
                         FStar_Syntax_Syntax.bind_repr = uu____3657;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____3658;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___443_3642.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____3692 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____3692
                       then
                         let uu____3697 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____3697
                       else ());
                      (let env =
                         let uu____3704 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____3704 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____3739 k =
                         match uu____3739 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____3759 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____3759 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____3768 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____3768 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____3769 =
                                          let uu____3776 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____3776 t1
                                           in
                                        (match uu____3769 with
                                         | (t2,uu____3778,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____3781 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____3781 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____3797 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____3799 =
                                               let uu____3801 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3801
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____3797 uu____3799
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____3816 ->
                                             let uu____3817 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____3824 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____3824 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____3817
                                             then (g_us, t3)
                                             else
                                               (let uu____3835 =
                                                  let uu____3841 =
                                                    let uu____3843 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____3845 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____3843
                                                      uu____3845
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____3841)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____3835
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____3853 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____3853
                        then
                          let uu____3858 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____3858
                        else ());
                       (let fresh_a_and_wp uu____3874 =
                          let fail1 t =
                            let uu____3887 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____3887
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____3903 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____3903 with
                          | (uu____3914,signature1) ->
                              let uu____3916 =
                                let uu____3917 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____3917.FStar_Syntax_Syntax.n  in
                              (match uu____3916 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____3927) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____3956)::(wp,uu____3958)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____3987 -> fail1 signature1)
                               | uu____3988 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4002 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4002
                          then
                            let uu____4007 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4007
                          else ()  in
                        let ret_wp =
                          let uu____4013 = fresh_a_and_wp ()  in
                          match uu____4013 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4029 =
                                  let uu____4038 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4045 =
                                    let uu____4054 =
                                      let uu____4061 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4061
                                       in
                                    [uu____4054]  in
                                  uu____4038 :: uu____4045  in
                                let uu____4080 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4029 uu____4080
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4088 = fresh_a_and_wp ()  in
                           match uu____4088 with
                           | (a,wp_sort_a) ->
                               let uu____4101 = fresh_a_and_wp ()  in
                               (match uu____4101 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4117 =
                                        let uu____4126 =
                                          let uu____4133 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4133
                                           in
                                        [uu____4126]  in
                                      let uu____4146 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4117
                                        uu____4146
                                       in
                                    let k =
                                      let uu____4152 =
                                        let uu____4161 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4168 =
                                          let uu____4177 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4184 =
                                            let uu____4193 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4200 =
                                              let uu____4209 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4216 =
                                                let uu____4225 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4225]  in
                                              uu____4209 :: uu____4216  in
                                            uu____4193 :: uu____4200  in
                                          uu____4177 :: uu____4184  in
                                        uu____4161 :: uu____4168  in
                                      let uu____4268 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4152
                                        uu____4268
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4276 = fresh_a_and_wp ()  in
                            match uu____4276 with
                            | (a,wp_sort_a) ->
                                let uu____4289 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4289 with
                                 | (t,uu____4295) ->
                                     let k =
                                       let uu____4299 =
                                         let uu____4308 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4315 =
                                           let uu____4324 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____4331 =
                                             let uu____4340 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____4340]  in
                                           uu____4324 :: uu____4331  in
                                         uu____4308 :: uu____4315  in
                                       let uu____4371 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4299
                                         uu____4371
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____4383 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____4383 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____4398 = fresh_a_and_wp ()  in
                                   match uu____4398 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____4412 =
                                           let uu____4415 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____4415
                                            in
                                         let uu____4416 =
                                           let uu____4417 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____4417
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____4412 uu____4416
                                          in
                                       let k =
                                         let uu____4429 =
                                           let uu____4438 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____4445 =
                                             let uu____4454 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____4461 =
                                               let uu____4470 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____4477 =
                                                 let uu____4486 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____4486]  in
                                               uu____4470 :: uu____4477  in
                                             uu____4454 :: uu____4461  in
                                           uu____4438 :: uu____4445  in
                                         let uu____4523 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____4429
                                           uu____4523
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____4531 = fresh_a_and_wp ()  in
                                     match uu____4531 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____4547 =
                                             let uu____4556 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____4563 =
                                               let uu____4572 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____4572]  in
                                             uu____4556 :: uu____4563  in
                                           let uu____4597 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____4547
                                             uu____4597
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____4605 = fresh_a_and_wp ()  in
                                      match uu____4605 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____4619 =
                                              let uu____4622 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____4622
                                               in
                                            let uu____4623 =
                                              let uu____4624 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____4624
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____4619 uu____4623
                                             in
                                          let wp_sort_b_a =
                                            let uu____4636 =
                                              let uu____4645 =
                                                let uu____4652 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____4652
                                                 in
                                              [uu____4645]  in
                                            let uu____4665 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4636 uu____4665
                                             in
                                          let k =
                                            let uu____4671 =
                                              let uu____4680 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____4687 =
                                                let uu____4696 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____4703 =
                                                  let uu____4712 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____4712]  in
                                                uu____4696 :: uu____4703  in
                                              uu____4680 :: uu____4687  in
                                            let uu____4743 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____4671 uu____4743
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
                             let uu____4753 = fresh_a_and_wp ()  in
                             match uu____4753 with
                             | (a,wp_sort_a) ->
                                 let uu____4768 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____4768 with
                                  | (t,uu____4776) ->
                                      let k =
                                        let uu____4780 =
                                          let uu____4789 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4796 =
                                            let uu____4805 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____4805]  in
                                          uu____4789 :: uu____4796  in
                                        let uu____4830 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____4780
                                          uu____4830
                                         in
                                      let trivial =
                                        let uu____4834 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____4834
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____4849 =
                             let uu____4860 =
                               let uu____4861 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____4861.FStar_Syntax_Syntax.n  in
                             match uu____4860 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____4880 ->
                                 let repr =
                                   let uu____4882 = fresh_a_and_wp ()  in
                                   match uu____4882 with
                                   | (a,wp_sort_a) ->
                                       let uu____4895 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____4895 with
                                        | (t,uu____4901) ->
                                            let k =
                                              let uu____4905 =
                                                let uu____4914 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____4921 =
                                                  let uu____4930 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____4930]  in
                                                uu____4914 :: uu____4921  in
                                              let uu____4955 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____4905 uu____4955
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____4975 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____4975 with
                                     | (uu____4982,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____4985 =
                                           let uu____4992 =
                                             let uu____4993 =
                                               let uu____5010 =
                                                 let uu____5021 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5038 =
                                                   let uu____5049 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5049]  in
                                                 uu____5021 :: uu____5038  in
                                               (repr2, uu____5010)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____4993
                                              in
                                           FStar_Syntax_Syntax.mk uu____4992
                                            in
                                         uu____4985
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5115 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5115 wp  in
                                   let destruct_repr t =
                                     let uu____5130 =
                                       let uu____5131 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5131.FStar_Syntax_Syntax.n  in
                                     match uu____5130 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5142,(t1,uu____5144)::
                                          (wp,uu____5146)::[])
                                         -> (t1, wp)
                                     | uu____5205 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5216 = fresh_a_and_wp ()  in
                                     match uu____5216 with
                                     | (a,uu____5224) ->
                                         let x_a =
                                           let uu____5230 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5230
                                            in
                                         let res =
                                           let wp =
                                             let uu____5238 =
                                               let uu____5243 =
                                                 let uu____5244 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5244
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5253 =
                                                 let uu____5254 =
                                                   let uu____5263 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5263
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5272 =
                                                   let uu____5283 =
                                                     let uu____5292 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5292
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5283]  in
                                                 uu____5254 :: uu____5272  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5243 uu____5253
                                                in
                                             uu____5238
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____5328 =
                                             let uu____5337 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5344 =
                                               let uu____5353 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____5353]  in
                                             uu____5337 :: uu____5344  in
                                           let uu____5378 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____5328
                                             uu____5378
                                            in
                                         let uu____5381 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____5381 with
                                          | (k1,uu____5389,uu____5390) ->
                                              let env1 =
                                                let uu____5394 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5394
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
                                        let uu____5405 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____5405
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____5406 = fresh_a_and_wp ()  in
                                      match uu____5406 with
                                      | (a,wp_sort_a) ->
                                          let uu____5419 = fresh_a_and_wp ()
                                             in
                                          (match uu____5419 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____5435 =
                                                   let uu____5444 =
                                                     let uu____5451 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____5451
                                                      in
                                                   [uu____5444]  in
                                                 let uu____5464 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5435 uu____5464
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
                                                 let uu____5472 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____5472
                                                  in
                                               let wp_g_x =
                                                 let uu____5477 =
                                                   let uu____5482 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____5483 =
                                                     let uu____5484 =
                                                       let uu____5493 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5493
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5484]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____5482 uu____5483
                                                    in
                                                 uu____5477
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____5524 =
                                                     let uu____5529 =
                                                       let uu____5530 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____5530
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____5539 =
                                                       let uu____5540 =
                                                         let uu____5543 =
                                                           let uu____5546 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____5547 =
                                                             let uu____5550 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____5551 =
                                                               let uu____5554
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____5555
                                                                 =
                                                                 let uu____5558
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____5558]
                                                                  in
                                                               uu____5554 ::
                                                                 uu____5555
                                                                in
                                                             uu____5550 ::
                                                               uu____5551
                                                              in
                                                           uu____5546 ::
                                                             uu____5547
                                                            in
                                                         r :: uu____5543  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____5540
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____5529 uu____5539
                                                      in
                                                   uu____5524
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____5576 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____5576
                                                 then
                                                   let uu____5587 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____5594 =
                                                     let uu____5603 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____5603]  in
                                                   uu____5587 :: uu____5594
                                                 else []  in
                                               let k =
                                                 let uu____5639 =
                                                   let uu____5648 =
                                                     let uu____5657 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____5664 =
                                                       let uu____5673 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____5673]  in
                                                     uu____5657 :: uu____5664
                                                      in
                                                   let uu____5698 =
                                                     let uu____5707 =
                                                       let uu____5716 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____5723 =
                                                         let uu____5732 =
                                                           let uu____5739 =
                                                             let uu____5740 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____5740
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____5739
                                                            in
                                                         let uu____5741 =
                                                           let uu____5750 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____5757 =
                                                             let uu____5766 =
                                                               let uu____5773
                                                                 =
                                                                 let uu____5774
                                                                   =
                                                                   let uu____5783
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____5783]
                                                                    in
                                                                 let uu____5802
                                                                   =
                                                                   let uu____5805
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____5805
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____5774
                                                                   uu____5802
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____5773
                                                                in
                                                             [uu____5766]  in
                                                           uu____5750 ::
                                                             uu____5757
                                                            in
                                                         uu____5732 ::
                                                           uu____5741
                                                          in
                                                       uu____5716 ::
                                                         uu____5723
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____5707
                                                      in
                                                   FStar_List.append
                                                     uu____5648 uu____5698
                                                    in
                                                 let uu____5850 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____5639 uu____5850
                                                  in
                                               let uu____5853 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____5853 with
                                                | (k1,uu____5861,uu____5862)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___644_5874 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___644_5874.FStar_TypeChecker_Env.strict_args_tab)
                                                         })
                                                        (fun _5876  ->
                                                           FStar_Pervasives_Native.Some
                                                             _5876)
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
                                         (let uu____5903 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____5917 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____5917 with
                                               | (usubst,uvs) ->
                                                   let uu____5940 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____5941 =
                                                     let uu___657_5942 = act
                                                        in
                                                     let uu____5943 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____5944 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___657_5942.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___657_5942.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___657_5942.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____5943;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5944
                                                     }  in
                                                   (uu____5940, uu____5941))
                                             in
                                          match uu____5903 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____5948 =
                                                  let uu____5949 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____5949.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5948 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____5975 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____5975
                                                    then
                                                      let uu____5978 =
                                                        let uu____5981 =
                                                          let uu____5982 =
                                                            let uu____5983 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____5983
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____5982
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____5981
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____5978
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6006 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6007 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6007 with
                                               | (act_typ1,uu____6015,g_t) ->
                                                   let env' =
                                                     let uu___674_6018 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___674_6018.FStar_TypeChecker_Env.strict_args_tab)
                                                     }  in
                                                   ((let uu____6021 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6021
                                                     then
                                                       let uu____6025 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6027 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6029 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6025
                                                         uu____6027
                                                         uu____6029
                                                     else ());
                                                    (let uu____6034 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6034 with
                                                     | (act_defn,uu____6042,g_a)
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
                                                         let uu____6046 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6082
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6082
                                                                with
                                                                | (bs2,uu____6094)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6101
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6101
                                                                     in
                                                                    let uu____6104
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6104
                                                                    with
                                                                    | 
                                                                    (k1,uu____6118,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6122 ->
                                                               let uu____6123
                                                                 =
                                                                 let uu____6129
                                                                   =
                                                                   let uu____6131
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6133
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6131
                                                                    uu____6133
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6129)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6123
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6046
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6151
                                                                  =
                                                                  let uu____6152
                                                                    =
                                                                    let uu____6153
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6153
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6152
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6151);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6155
                                                                    =
                                                                    let uu____6156
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6156.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6155
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6181
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6181
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6188
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6188
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6208
                                                                    =
                                                                    let uu____6209
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6209]
                                                                     in
                                                                    let uu____6210
                                                                    =
                                                                    let uu____6221
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6221]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6208;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6210;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6246
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6246))
                                                                  | uu____6249
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6251
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
                                                                    let uu____6273
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6273))
                                                                   in
                                                                match uu____6251
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
                                                                    let uu___724_6292
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___724_6292.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___724_6292.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___724_6292.FStar_Syntax_Syntax.action_params);
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
                           match uu____4849 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6317 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6317
                                   ts1
                                  in
                               let ed3 =
                                 let uu___736_6327 = ed2  in
                                 let uu____6328 = cl signature  in
                                 let uu____6329 = cl ret_wp  in
                                 let uu____6330 = cl bind_wp  in
                                 let uu____6331 = cl stronger  in
                                 let uu____6332 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____6337 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____6340 = cl repr  in
                                 let uu____6341 = cl return_repr  in
                                 let uu____6342 = cl bind_repr  in
                                 let uu____6343 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___739_6351 = a  in
                                        let uu____6352 =
                                          let uu____6353 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____6353
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____6378 =
                                          let uu____6379 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____6379
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___739_6351.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___739_6351.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___739_6351.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___739_6351.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____6352;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____6378
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___736_6327.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___736_6327.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___736_6327.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___736_6327.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___736_6327.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____6328;
                                   FStar_Syntax_Syntax.ret_wp = uu____6329;
                                   FStar_Syntax_Syntax.bind_wp = uu____6330;
                                   FStar_Syntax_Syntax.stronger = uu____6331;
                                   FStar_Syntax_Syntax.match_wps = uu____6332;
                                   FStar_Syntax_Syntax.trivial = uu____6337;
                                   FStar_Syntax_Syntax.repr = uu____6340;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____6341;
                                   FStar_Syntax_Syntax.bind_repr = uu____6342;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____6343;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___736_6327.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____6405 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____6405
                                 then
                                   let uu____6410 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____6410
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
        let fail1 uu____6463 =
          let uu____6464 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____6470 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____6464 uu____6470  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____6514)::(wp,uu____6516)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____6545 -> fail1 ())
        | uu____6546 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____6559 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____6559
       then
         let uu____6564 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____6564
       else ());
      (let uu____6569 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____6569 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           let uu____6615 =
             if (FStar_List.length us) = Prims.int_zero
             then (env0, us, lift)
             else
               (let uu____6639 = FStar_Syntax_Subst.open_univ_vars us lift
                   in
                match uu____6639 with
                | (us1,lift1) ->
                    let uu____6654 =
                      FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                    (uu____6654, us1, lift1))
              in
           (match uu____6615 with
            | (env,us1,lift1) ->
                let uu____6664 =
                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                (match uu____6664 with
                 | (lift2,lc,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let lift_ty =
                         FStar_All.pipe_right
                           lc.FStar_TypeChecker_Common.res_typ
                           (FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env0)
                          in
                       (let uu____6677 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "LayeredEffects")
                           in
                        if uu____6677
                        then
                          let uu____6682 =
                            FStar_Syntax_Print.term_to_string lift2  in
                          let uu____6684 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.print2
                            "Typechecked lift: %s and lift_ty: %s\n"
                            uu____6682 uu____6684
                        else ());
                       (let lift_t_shape_error s =
                          let uu____6698 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.source
                             in
                          let uu____6700 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.target
                             in
                          let uu____6702 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.format4
                            "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                            uu____6698 uu____6700 s uu____6702
                           in
                        let uu____6705 =
                          let uu____6712 =
                            let uu____6717 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____6717
                              (fun uu____6734  ->
                                 match uu____6734 with
                                 | (t,u) ->
                                     let uu____6745 =
                                       let uu____6746 =
                                         FStar_Syntax_Syntax.gen_bv "a"
                                           FStar_Pervasives_Native.None t
                                          in
                                       FStar_All.pipe_right uu____6746
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____6745, u))
                             in
                          match uu____6712 with
                          | (a,u_a) ->
                              let uu____6756 =
                                let uu____6763 =
                                  FStar_TypeChecker_Env.lookup_effect_lid env
                                    sub1.FStar_Syntax_Syntax.source
                                   in
                                monad_signature env
                                  sub1.FStar_Syntax_Syntax.source uu____6763
                                 in
                              (match uu____6756 with
                               | (a',wp_sort_a') ->
                                   let src_wp_sort_a =
                                     let uu____6777 =
                                       let uu____6780 =
                                         let uu____6781 =
                                           let uu____6788 =
                                             let uu____6791 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____6791
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           (a', uu____6788)  in
                                         FStar_Syntax_Syntax.NT uu____6781
                                          in
                                       [uu____6780]  in
                                     FStar_Syntax_Subst.subst uu____6777
                                       wp_sort_a'
                                      in
                                   let wp =
                                     let uu____6811 =
                                       FStar_Syntax_Syntax.gen_bv "wp"
                                         FStar_Pervasives_Native.None
                                         src_wp_sort_a
                                        in
                                     FStar_All.pipe_right uu____6811
                                       FStar_Syntax_Syntax.mk_binder
                                      in
                                   let rest_bs =
                                     let uu____6828 =
                                       let uu____6829 =
                                         FStar_Syntax_Subst.compress lift_ty
                                          in
                                       uu____6829.FStar_Syntax_Syntax.n  in
                                     match uu____6828 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____6841) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (3))
                                         ->
                                         let uu____6869 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____6869 with
                                          | (a'1,uu____6879)::(wp',uu____6881)::bs1
                                              ->
                                              let uu____6911 =
                                                let uu____6912 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____6912
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____7010 =
                                                let uu____7023 =
                                                  let uu____7026 =
                                                    let uu____7027 =
                                                      let uu____7034 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a'1, uu____7034)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____7027
                                                     in
                                                  let uu____7041 =
                                                    let uu____7044 =
                                                      let uu____7045 =
                                                        let uu____7052 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            (FStar_Pervasives_Native.fst
                                                               wp)
                                                           in
                                                        (wp', uu____7052)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____7045
                                                       in
                                                    [uu____7044]  in
                                                  uu____7026 :: uu____7041
                                                   in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____7023
                                                 in
                                              FStar_All.pipe_right uu____6911
                                                uu____7010)
                                     | uu____7067 ->
                                         let uu____7068 =
                                           let uu____7074 =
                                             lift_t_shape_error
                                               "either not an arrow, or not enough binders"
                                              in
                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                             uu____7074)
                                            in
                                         FStar_Errors.raise_error uu____7068
                                           r
                                      in
                                   let f =
                                     let f_sort =
                                       let uu____7096 =
                                         let uu____7105 =
                                           FStar_Syntax_Syntax.null_binder
                                             FStar_Syntax_Syntax.t_unit
                                            in
                                         [uu____7105]  in
                                       let uu____7124 =
                                         let uu____7127 =
                                           let uu____7128 =
                                             let uu____7131 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____7131
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           let uu____7142 =
                                             let uu____7153 =
                                               let uu____7162 =
                                                 let uu____7163 =
                                                   FStar_All.pipe_right wp
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____7163
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7162
                                                 FStar_Syntax_Syntax.as_arg
                                                in
                                             [uu____7153]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               [u_a];
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (sub1.FStar_Syntax_Syntax.source);
                                             FStar_Syntax_Syntax.result_typ =
                                               uu____7128;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7142;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7127
                                          in
                                       FStar_Syntax_Util.arrow uu____7096
                                         uu____7124
                                        in
                                     let uu____7196 =
                                       FStar_Syntax_Syntax.gen_bv "f"
                                         FStar_Pervasives_Native.None f_sort
                                        in
                                     FStar_All.pipe_right uu____7196
                                       FStar_Syntax_Syntax.mk_binder
                                      in
                                   let bs = a :: wp ::
                                     (FStar_List.append rest_bs [f])  in
                                   let uu____7243 =
                                     let uu____7248 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____7249 =
                                       let uu____7250 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7250
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_layered_effect_repr_en
                                       uu____7248 r
                                       sub1.FStar_Syntax_Syntax.target u_a
                                       uu____7249
                                      in
                                   (match uu____7243 with
                                    | (repr,g_repr) ->
                                        let uu____7267 =
                                          let uu____7270 =
                                            let uu____7273 =
                                              let uu____7276 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              FStar_All.pipe_right uu____7276
                                                (fun _7279  ->
                                                   FStar_Pervasives_Native.Some
                                                     _7279)
                                               in
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr uu____7273
                                             in
                                          FStar_Syntax_Util.arrow bs
                                            uu____7270
                                           in
                                        (uu____7267, g_repr)))
                           in
                        match uu____6705 with
                        | (k,g_k) ->
                            ((let uu____7289 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____7289
                              then
                                let uu____7294 =
                                  FStar_Syntax_Print.term_to_string k  in
                                FStar_Util.print1
                                  "tc_layered_lift: before unification k: %s\n"
                                  uu____7294
                              else ());
                             (let g1 =
                                FStar_TypeChecker_Rel.teq env lift_ty k  in
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g_k;
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g1;
                              (let uu____7303 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env0)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____7303
                               then
                                 let uu____7308 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "After unification k: %s\n" uu____7308
                               else ());
                              (let uu____7313 =
                                 let uu____7326 =
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 lift2
                                    in
                                 match uu____7326 with
                                 | (inst_us,lift3) ->
                                     (if
                                        (FStar_List.length inst_us) <>
                                          Prims.int_one
                                      then
                                        (let uu____7353 =
                                           let uu____7359 =
                                             let uu____7361 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.source
                                                in
                                             let uu____7363 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.target
                                                in
                                             let uu____7365 =
                                               let uu____7367 =
                                                 FStar_All.pipe_right inst_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7367
                                                 FStar_Util.string_of_int
                                                in
                                             let uu____7374 =
                                               FStar_Syntax_Print.term_to_string
                                                 lift3
                                                in
                                             FStar_Util.format4
                                               "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                               uu____7361 uu____7363
                                               uu____7365 uu____7374
                                              in
                                           (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                             uu____7359)
                                            in
                                         FStar_Errors.raise_error uu____7353
                                           r)
                                      else ();
                                      (let uu____7380 =
                                         ((FStar_List.length us1) =
                                            Prims.int_zero)
                                           ||
                                           (((FStar_List.length us1) =
                                               (FStar_List.length inst_us))
                                              &&
                                              (FStar_List.forall2
                                                 (fun u1  ->
                                                    fun u2  ->
                                                      let uu____7389 =
                                                        FStar_Syntax_Syntax.order_univ_name
                                                          u1 u2
                                                         in
                                                      uu____7389 =
                                                        Prims.int_zero) us1
                                                 inst_us))
                                          in
                                       if uu____7380
                                       then
                                         let uu____7406 =
                                           let uu____7409 =
                                             FStar_All.pipe_right k
                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____7409
                                             (FStar_Syntax_Subst.close_univ_vars
                                                inst_us)
                                            in
                                         (inst_us, lift3, uu____7406)
                                       else
                                         (let uu____7420 =
                                            let uu____7426 =
                                              let uu____7428 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____7430 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____7432 =
                                                let uu____7434 =
                                                  FStar_All.pipe_right us1
                                                    FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7434
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7441 =
                                                let uu____7443 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7443
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7450 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format5
                                                "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                uu____7428 uu____7430
                                                uu____7432 uu____7441
                                                uu____7450
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____7426)
                                             in
                                          FStar_Errors.raise_error uu____7420
                                            r)))
                                  in
                               match uu____7313 with
                               | (us2,lift3,lift_wp) ->
                                   let sub2 =
                                     let uu___847_7482 = sub1  in
                                     {
                                       FStar_Syntax_Syntax.source =
                                         (uu___847_7482.FStar_Syntax_Syntax.source);
                                       FStar_Syntax_Syntax.target =
                                         (uu___847_7482.FStar_Syntax_Syntax.target);
                                       FStar_Syntax_Syntax.lift_wp =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift_wp));
                                       FStar_Syntax_Syntax.lift =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift3))
                                     }  in
                                   ((let uu____7492 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env0)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____7492
                                     then
                                       let uu____7497 =
                                         FStar_Syntax_Print.sub_eff_to_string
                                           sub2
                                          in
                                       FStar_Util.print1
                                         "Final sub_effect: %s\n" uu____7497
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
          (let uu____7523 =
             let uu____7530 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____7530
              in
           match uu____7523 with
           | (a,wp_a_src) ->
               let uu____7537 =
                 let uu____7544 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____7544
                  in
               (match uu____7537 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____7552 =
                        let uu____7555 =
                          let uu____7556 =
                            let uu____7563 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____7563)  in
                          FStar_Syntax_Syntax.NT uu____7556  in
                        [uu____7555]  in
                      FStar_Syntax_Subst.subst uu____7552 wp_b_tgt  in
                    let expected_k =
                      let uu____7571 =
                        let uu____7580 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____7587 =
                          let uu____7596 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____7596]  in
                        uu____7580 :: uu____7587  in
                      let uu____7621 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____7571 uu____7621  in
                    let repr_type eff_name a1 wp =
                      (let uu____7643 =
                         let uu____7645 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____7645  in
                       if uu____7643
                       then
                         let uu____7648 =
                           let uu____7654 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____7654)
                            in
                         let uu____7658 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____7648 uu____7658
                       else ());
                      (let uu____7661 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____7661 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____7694 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____7695 =
                             let uu____7702 =
                               let uu____7703 =
                                 let uu____7720 =
                                   let uu____7731 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____7740 =
                                     let uu____7751 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____7751]  in
                                   uu____7731 :: uu____7740  in
                                 (repr, uu____7720)  in
                               FStar_Syntax_Syntax.Tm_app uu____7703  in
                             FStar_Syntax_Syntax.mk uu____7702  in
                           uu____7695 FStar_Pervasives_Native.None uu____7694)
                       in
                    let uu____7796 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____7969 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____7980 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____7980 with
                              | (usubst,uvs1) ->
                                  let uu____8003 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8004 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8003, uu____8004)
                            else (env, lift_wp)  in
                          (match uu____7969 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8054 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8054))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8125 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8140 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8140 with
                              | (usubst,uvs) ->
                                  let uu____8165 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8165)
                            else ([], lift)  in
                          (match uu____8125 with
                           | (uvs,lift1) ->
                               ((let uu____8201 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____8201
                                 then
                                   let uu____8205 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____8205
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____8211 =
                                   let uu____8218 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____8218 lift1
                                    in
                                 match uu____8211 with
                                 | (lift2,comp,uu____8243) ->
                                     let uu____8244 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8244 with
                                      | (uu____8273,lift_wp,lift_elab) ->
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
                                            let uu____8305 =
                                              let uu____8316 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8316
                                               in
                                            let uu____8333 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8305, uu____8333)
                                          else
                                            (let uu____8362 =
                                               let uu____8373 =
                                                 let uu____8382 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8382)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8373
                                                in
                                             let uu____8397 =
                                               let uu____8406 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8406)  in
                                             (uu____8362, uu____8397))))))
                       in
                    (match uu____7796 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___927_8470 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___927_8470.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___927_8470.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___927_8470.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___927_8470.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___927_8470.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___927_8470.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___927_8470.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___927_8470.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___927_8470.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___927_8470.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___927_8470.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___927_8470.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___927_8470.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___927_8470.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___927_8470.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___927_8470.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___927_8470.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___927_8470.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___927_8470.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___927_8470.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___927_8470.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___927_8470.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___927_8470.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___927_8470.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___927_8470.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___927_8470.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___927_8470.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___927_8470.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___927_8470.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___927_8470.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___927_8470.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___927_8470.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___927_8470.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___927_8470.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___927_8470.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___927_8470.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___927_8470.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___927_8470.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___927_8470.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___927_8470.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___927_8470.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___927_8470.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___927_8470.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___927_8470.FStar_TypeChecker_Env.strict_args_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____8503 =
                                 let uu____8508 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____8508 with
                                 | (usubst,uvs1) ->
                                     let uu____8531 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____8532 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____8531, uu____8532)
                                  in
                               (match uu____8503 with
                                | (env2,lift2) ->
                                    let uu____8537 =
                                      let uu____8544 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____8544
                                       in
                                    (match uu____8537 with
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
                                             let uu____8570 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____8571 =
                                               let uu____8578 =
                                                 let uu____8579 =
                                                   let uu____8596 =
                                                     let uu____8607 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____8616 =
                                                       let uu____8627 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____8627]  in
                                                     uu____8607 :: uu____8616
                                                      in
                                                   (lift_wp1, uu____8596)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____8579
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____8578
                                                in
                                             uu____8571
                                               FStar_Pervasives_Native.None
                                               uu____8570
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____8675 =
                                             let uu____8684 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____8691 =
                                               let uu____8700 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____8707 =
                                                 let uu____8716 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____8716]  in
                                               uu____8700 :: uu____8707  in
                                             uu____8684 :: uu____8691  in
                                           let uu____8747 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____8675
                                             uu____8747
                                            in
                                         let uu____8750 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____8750 with
                                          | (expected_k2,uu____8760,uu____8761)
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
                                                   let uu____8769 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____8769))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____8777 =
                             let uu____8779 =
                               let uu____8781 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____8781
                                 FStar_List.length
                                in
                             uu____8779 <> Prims.int_one  in
                           if uu____8777
                           then
                             let uu____8804 =
                               let uu____8810 =
                                 let uu____8812 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8814 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8816 =
                                   let uu____8818 =
                                     let uu____8820 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8820
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8818
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8812 uu____8814 uu____8816
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8810)
                                in
                             FStar_Errors.raise_error uu____8804 r
                           else ());
                          (let uu____8847 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____8850 =
                                  let uu____8852 =
                                    let uu____8855 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____8855
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8852
                                    FStar_List.length
                                   in
                                uu____8850 <> Prims.int_one)
                              in
                           if uu____8847
                           then
                             let uu____8893 =
                               let uu____8899 =
                                 let uu____8901 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____8903 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____8905 =
                                   let uu____8907 =
                                     let uu____8909 =
                                       let uu____8912 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____8912
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8909
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____8907
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____8901 uu____8903 uu____8905
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____8899)
                                in
                             FStar_Errors.raise_error uu____8893 r
                           else ());
                          (let uu___964_8954 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___964_8954.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___964_8954.FStar_Syntax_Syntax.target);
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
    fun uu____8985  ->
      fun r  ->
        match uu____8985 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9008 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9036 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9036 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9067 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9067 c  in
                     let uu____9076 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9076, uvs1, tps1, c1))
               in
            (match uu____9008 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9096 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9096 with
                  | (tps2,c2) ->
                      let uu____9111 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9111 with
                       | (tps3,env3,us) ->
                           let uu____9129 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____9129 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____9155)::uu____9156 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____9175 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____9183 =
                                    let uu____9185 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____9185  in
                                  if uu____9183
                                  then
                                    let uu____9188 =
                                      let uu____9194 =
                                        let uu____9196 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____9198 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____9196 uu____9198
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____9194)
                                       in
                                    FStar_Errors.raise_error uu____9188 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____9206 =
                                    let uu____9207 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____9207
                                     in
                                  match uu____9206 with
                                  | (uvs2,t) ->
                                      let uu____9236 =
                                        let uu____9241 =
                                          let uu____9254 =
                                            let uu____9255 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____9255.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____9254)  in
                                        match uu____9241 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____9270,c5)) -> ([], c5)
                                        | (uu____9312,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____9351 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____9236 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____9383 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____9383 with
                                               | (uu____9388,t1) ->
                                                   let uu____9390 =
                                                     let uu____9396 =
                                                       let uu____9398 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____9400 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____9404 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____9398
                                                         uu____9400
                                                         uu____9404
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____9396)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____9390 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  