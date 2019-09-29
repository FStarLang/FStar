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
           FStar_TypeChecker_Util.fresh_effect_repr env r
             ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
            in
         let not_an_arrow_error comb n1 t r =
           let uu____808 =
             let uu____814 =
               let uu____816 = FStar_Util.string_of_int n1  in
               let uu____818 = FStar_Syntax_Print.tag_of_term t  in
               let uu____820 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.format5
                 "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                 uu____816 uu____818 uu____820
                in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____814)  in
           FStar_Errors.raise_error uu____808 r  in
         let return_repr =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
              in
           let uu____850 =
             check_and_gen "return_repr" Prims.int_one
               ed.FStar_Syntax_Syntax.return_repr
              in
           match uu____850 with
           | (ret_us,ret_t,ret_ty) ->
               let uu____874 =
                 FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
               (match uu____874 with
                | (us,ty) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____894 = fresh_a_and_u_a "a"  in
                    (match uu____894 with
                     | (a,u_a) ->
                         let rest_bs =
                           let uu____923 =
                             let uu____924 = FStar_Syntax_Subst.compress ty
                                in
                             uu____924.FStar_Syntax_Syntax.n  in
                           match uu____923 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____936) when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____964 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____964 with
                                | (a',uu____974)::bs1 ->
                                    let uu____994 =
                                      let uu____995 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one))
                                         in
                                      FStar_All.pipe_right uu____995
                                        FStar_Pervasives_Native.fst
                                       in
                                    let uu____1061 =
                                      let uu____1074 =
                                        let uu____1077 =
                                          let uu____1078 =
                                            let uu____1085 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a)
                                               in
                                            (a', uu____1085)  in
                                          FStar_Syntax_Syntax.NT uu____1078
                                           in
                                        [uu____1077]  in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____1074
                                       in
                                    FStar_All.pipe_right uu____994 uu____1061)
                           | uu____1100 ->
                               not_an_arrow_error "return" (Prims.of_int (2))
                                 ty r
                            in
                         let bs =
                           let uu____1112 =
                             let uu____1121 =
                               let uu____1130 = fresh_x_a "x" a  in
                               [uu____1130]  in
                             FStar_List.append rest_bs uu____1121  in
                           a :: uu____1112  in
                         let uu____1162 =
                           let uu____1167 =
                             FStar_TypeChecker_Env.push_binders env bs  in
                           let uu____1168 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.fst a)
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           fresh_repr r uu____1167 u_a uu____1168  in
                         (match uu____1162 with
                          | (repr1,g) ->
                              let k =
                                let uu____1188 =
                                  FStar_Syntax_Syntax.mk_Total' repr1
                                    (FStar_Pervasives_Native.Some u_a)
                                   in
                                FStar_Syntax_Util.arrow bs uu____1188  in
                              let g_eq = FStar_TypeChecker_Rel.teq env ty k
                                 in
                              ((let uu____1193 =
                                  FStar_TypeChecker_Env.conj_guard g g_eq  in
                                FStar_TypeChecker_Rel.force_trivial_guard env
                                  uu____1193);
                               (let uu____1194 =
                                  let uu____1197 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env)
                                     in
                                  FStar_Syntax_Subst.close_univ_vars us
                                    uu____1197
                                   in
                                (ret_us, ret_t, uu____1194))))))
            in
         log_combinator "return_repr" return_repr;
         (let bind_repr =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
               in
            let uu____1224 =
              check_and_gen "bind_repr" (Prims.of_int (2))
                ed.FStar_Syntax_Syntax.bind_repr
               in
            match uu____1224 with
            | (bind_us,bind_t,bind_ty) ->
                let uu____1248 =
                  FStar_Syntax_Subst.open_univ_vars bind_us bind_ty  in
                (match uu____1248 with
                 | (us,ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                        in
                     let uu____1268 = fresh_a_and_u_a "a"  in
                     (match uu____1268 with
                      | (a,u_a) ->
                          let uu____1288 = fresh_a_and_u_a "b"  in
                          (match uu____1288 with
                           | (b,u_b) ->
                               let rest_bs =
                                 let uu____1317 =
                                   let uu____1318 =
                                     FStar_Syntax_Subst.compress ty  in
                                   uu____1318.FStar_Syntax_Syntax.n  in
                                 match uu____1317 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____1330) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (4))
                                     ->
                                     let uu____1358 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____1358 with
                                      | (a',uu____1368)::(b',uu____1370)::bs1
                                          ->
                                          let uu____1400 =
                                            let uu____1401 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      (Prims.of_int (2))))
                                               in
                                            FStar_All.pipe_right uu____1401
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____1499 =
                                            let uu____1512 =
                                              let uu____1515 =
                                                let uu____1516 =
                                                  let uu____1523 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____1523)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____1516
                                                 in
                                              let uu____1530 =
                                                let uu____1533 =
                                                  let uu____1534 =
                                                    let uu____1541 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           b)
                                                       in
                                                    (b', uu____1541)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1534
                                                   in
                                                [uu____1533]  in
                                              uu____1515 :: uu____1530  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____1512
                                             in
                                          FStar_All.pipe_right uu____1400
                                            uu____1499)
                                 | uu____1556 ->
                                     not_an_arrow_error "bind"
                                       (Prims.of_int (4)) ty r
                                  in
                               let bs = a :: b :: rest_bs  in
                               let uu____1580 =
                                 let uu____1591 =
                                   let uu____1596 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1597 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1596 u_a uu____1597  in
                                 match uu____1591 with
                                 | (repr1,g) ->
                                     let uu____1612 =
                                       let uu____1619 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1
                                          in
                                       FStar_All.pipe_right uu____1619
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____1612, g)
                                  in
                               (match uu____1580 with
                                | (f,guard_f) ->
                                    let uu____1659 =
                                      let x_a = fresh_x_a "x" a  in
                                      let uu____1672 =
                                        let uu____1677 =
                                          FStar_TypeChecker_Env.push_binders
                                            env (FStar_List.append bs [x_a])
                                           in
                                        let uu____1696 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst b)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____1677 u_b
                                          uu____1696
                                         in
                                      match uu____1672 with
                                      | (repr1,g) ->
                                          let uu____1711 =
                                            let uu____1718 =
                                              let uu____1719 =
                                                let uu____1720 =
                                                  let uu____1723 =
                                                    let uu____1726 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        ()
                                                       in
                                                    FStar_Pervasives_Native.Some
                                                      uu____1726
                                                     in
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1 uu____1723
                                                   in
                                                FStar_Syntax_Util.arrow 
                                                  [x_a] uu____1720
                                                 in
                                              FStar_Syntax_Syntax.gen_bv "g"
                                                FStar_Pervasives_Native.None
                                                uu____1719
                                               in
                                            FStar_All.pipe_right uu____1718
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____1711, g)
                                       in
                                    (match uu____1659 with
                                     | (g,guard_g) ->
                                         let uu____1778 =
                                           let uu____1783 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1784 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1783 u_b
                                             uu____1784
                                            in
                                         (match uu____1778 with
                                          | (repr1,guard_repr) ->
                                              let k =
                                                let uu____1804 =
                                                  FStar_Syntax_Syntax.mk_Total'
                                                    repr1
                                                    (FStar_Pervasives_Native.Some
                                                       u_b)
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs
                                                     [f; g]) uu____1804
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
                                               (let uu____1833 =
                                                  let uu____1836 =
                                                    FStar_All.pipe_right k
                                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                         env)
                                                     in
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    bind_us uu____1836
                                                   in
                                                (bind_us, bind_t, uu____1833)))))))))
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
             let uu____1878 =
               check_and_gen "stronger_repr" Prims.int_one stronger_repr  in
             match uu____1878 with
             | (stronger_us,stronger_t,stronger_ty) ->
                 ((let uu____1903 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                       (FStar_Options.Other "LayeredEffects")
                      in
                   if uu____1903
                   then
                     let uu____1908 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_t)
                        in
                     let uu____1914 =
                       FStar_Syntax_Print.tscheme_to_string
                         (stronger_us, stronger_ty)
                        in
                     FStar_Util.print2
                       "stronger combinator typechecked with term: %s and type: %s\n"
                       uu____1908 uu____1914
                   else ());
                  (let uu____1923 =
                     FStar_Syntax_Subst.open_univ_vars stronger_us
                       stronger_ty
                      in
                   match uu____1923 with
                   | (us,ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                          in
                       let uu____1943 = fresh_a_and_u_a "a"  in
                       (match uu____1943 with
                        | (a,u) ->
                            let rest_bs =
                              let uu____1972 =
                                let uu____1973 =
                                  FStar_Syntax_Subst.compress ty  in
                                uu____1973.FStar_Syntax_Syntax.n  in
                              match uu____1972 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1985)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____2013 =
                                    FStar_Syntax_Subst.open_binders bs  in
                                  (match uu____2013 with
                                   | (a',uu____2023)::bs1 ->
                                       let uu____2043 =
                                         let uu____2044 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.splitAt
                                                ((FStar_List.length bs1) -
                                                   Prims.int_one))
                                            in
                                         FStar_All.pipe_right uu____2044
                                           FStar_Pervasives_Native.fst
                                          in
                                       let uu____2142 =
                                         let uu____2155 =
                                           let uu____2158 =
                                             let uu____2159 =
                                               let uu____2166 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      a)
                                                  in
                                               (a', uu____2166)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2159
                                              in
                                           [uu____2158]  in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____2155
                                          in
                                       FStar_All.pipe_right uu____2043
                                         uu____2142)
                              | uu____2181 ->
                                  not_an_arrow_error "stronger"
                                    (Prims.of_int (2)) ty r
                               in
                            let bs = a :: rest_bs  in
                            let uu____2199 =
                              let uu____2210 =
                                let uu____2215 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____2216 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                fresh_repr r uu____2215 u uu____2216  in
                              match uu____2210 with
                              | (repr1,g) ->
                                  let uu____2231 =
                                    let uu____2238 =
                                      FStar_Syntax_Syntax.gen_bv "f"
                                        FStar_Pervasives_Native.None repr1
                                       in
                                    FStar_All.pipe_right uu____2238
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____2231, g)
                               in
                            (match uu____2199 with
                             | (f,guard_f) ->
                                 let uu____2278 =
                                   let uu____2283 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____2284 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____2283 u uu____2284  in
                                 (match uu____2278 with
                                  | (ret_t,guard_ret_t) ->
                                      let pure_wp_t =
                                        let pure_wp_ts =
                                          let uu____2303 =
                                            FStar_TypeChecker_Env.lookup_definition
                                              [FStar_TypeChecker_Env.NoDelta]
                                              env
                                              FStar_Parser_Const.pure_wp_lid
                                             in
                                          FStar_All.pipe_right uu____2303
                                            FStar_Util.must
                                           in
                                        let uu____2320 =
                                          FStar_TypeChecker_Env.inst_tscheme
                                            pure_wp_ts
                                           in
                                        match uu____2320 with
                                        | (uu____2325,pure_wp_t) ->
                                            let uu____2327 =
                                              let uu____2332 =
                                                let uu____2333 =
                                                  FStar_All.pipe_right ret_t
                                                    FStar_Syntax_Syntax.as_arg
                                                   in
                                                [uu____2333]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                pure_wp_t uu____2332
                                               in
                                            uu____2327
                                              FStar_Pervasives_Native.None r
                                         in
                                      let uu____2366 =
                                        let reason =
                                          FStar_Util.format1
                                            "implicit for pure_wp in checking stronger for %s"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                           in
                                        let uu____2382 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        FStar_TypeChecker_Util.new_implicit_var
                                          reason r uu____2382 pure_wp_t
                                         in
                                      (match uu____2366 with
                                       | (pure_wp_uvar,uu____2396,guard_wp)
                                           ->
                                           let c =
                                             let uu____2411 =
                                               let uu____2412 =
                                                 let uu____2413 =
                                                   FStar_TypeChecker_Env.new_u_univ
                                                     ()
                                                    in
                                                 [uu____2413]  in
                                               let uu____2414 =
                                                 let uu____2425 =
                                                   FStar_All.pipe_right
                                                     pure_wp_uvar
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 [uu____2425]  in
                                               {
                                                 FStar_Syntax_Syntax.comp_univs
                                                   = uu____2412;
                                                 FStar_Syntax_Syntax.effect_name
                                                   =
                                                   FStar_Parser_Const.effect_PURE_lid;
                                                 FStar_Syntax_Syntax.result_typ
                                                   = ret_t;
                                                 FStar_Syntax_Syntax.effect_args
                                                   = uu____2414;
                                                 FStar_Syntax_Syntax.flags =
                                                   []
                                               }  in
                                             FStar_Syntax_Syntax.mk_Comp
                                               uu____2411
                                              in
                                           let k =
                                             FStar_Syntax_Util.arrow
                                               (FStar_List.append bs [f]) c
                                              in
                                           ((let uu____2480 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____2480
                                             then
                                               let uu____2485 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected type before unification: %s\n"
                                                 uu____2485
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
                                              let uu____2493 =
                                                let uu____2496 =
                                                  FStar_All.pipe_right k1
                                                    (FStar_TypeChecker_Normalize.normalize
                                                       [FStar_TypeChecker_Env.Beta;
                                                       FStar_TypeChecker_Env.Eager_unfolding]
                                                       env)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2496
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     stronger_us)
                                                 in
                                              (stronger_us, stronger_t,
                                                uu____2493))))))))))
              in
           log_combinator "stronger_repr" stronger_repr;
           (let conjunction =
              let conjunction_ts =
                let uu____2521 =
                  FStar_All.pipe_right ed.FStar_Syntax_Syntax.match_wps
                    FStar_Util.right
                   in
                uu____2521.FStar_Syntax_Syntax.conjunction  in
              let r =
                (FStar_Pervasives_Native.snd conjunction_ts).FStar_Syntax_Syntax.pos
                 in
              let uu____2531 =
                check_and_gen "conjunction" Prims.int_one conjunction_ts  in
              match uu____2531 with
              | (conjunction_us,conjunction_t,conjunction_ty) ->
                  let uu____2555 =
                    FStar_Syntax_Subst.open_univ_vars conjunction_us
                      conjunction_t
                     in
                  (match uu____2555 with
                   | (us,t) ->
                       let uu____2574 =
                         FStar_Syntax_Subst.open_univ_vars conjunction_us
                           conjunction_ty
                          in
                       (match uu____2574 with
                        | (uu____2591,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____2594 = fresh_a_and_u_a "a"  in
                            (match uu____2594 with
                             | (a,u_a) ->
                                 let rest_bs =
                                   let uu____2623 =
                                     let uu____2624 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____2624.FStar_Syntax_Syntax.n  in
                                   match uu____2623 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____2636) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (4))
                                       ->
                                       let uu____2664 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____2664 with
                                        | (a',uu____2674)::bs1 ->
                                            let uu____2694 =
                                              let uu____2695 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - (Prims.of_int (3))))
                                                 in
                                              FStar_All.pipe_right uu____2695
                                                FStar_Pervasives_Native.fst
                                               in
                                            let uu____2793 =
                                              let uu____2806 =
                                                let uu____2809 =
                                                  let uu____2810 =
                                                    let uu____2817 =
                                                      let uu____2820 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____2820
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    (a', uu____2817)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____2810
                                                   in
                                                [uu____2809]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____2806
                                               in
                                            FStar_All.pipe_right uu____2694
                                              uu____2793)
                                   | uu____2841 ->
                                       not_an_arrow_error "conjunction"
                                         (Prims.of_int (4)) ty r
                                    in
                                 let bs = a :: rest_bs  in
                                 let uu____2859 =
                                   let uu____2870 =
                                     let uu____2875 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____2876 =
                                       let uu____2877 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____2877
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     fresh_repr r uu____2875 u_a uu____2876
                                      in
                                   match uu____2870 with
                                   | (repr1,g) ->
                                       let uu____2898 =
                                         let uu____2905 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1
                                            in
                                         FStar_All.pipe_right uu____2905
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____2898, g)
                                    in
                                 (match uu____2859 with
                                  | (f_bs,guard_f) ->
                                      let uu____2945 =
                                        let uu____2956 =
                                          let uu____2961 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2962 =
                                            let uu____2963 =
                                              FStar_All.pipe_right a
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_All.pipe_right uu____2963
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2961 u_a
                                            uu____2962
                                           in
                                        match uu____2956 with
                                        | (repr1,g) ->
                                            let uu____2984 =
                                              let uu____2991 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "g"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____2991
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____2984, g)
                                         in
                                      (match uu____2945 with
                                       | (g_bs,guard_g) ->
                                           let p_b =
                                             let uu____3038 =
                                               FStar_Syntax_Syntax.gen_bv "p"
                                                 FStar_Pervasives_Native.None
                                                 FStar_Syntax_Util.ktype0
                                                in
                                             FStar_All.pipe_right uu____3038
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           let uu____3046 =
                                             let uu____3051 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env
                                                 (FStar_List.append bs [p_b])
                                                in
                                             let uu____3070 =
                                               let uu____3071 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3071
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3051 u_a
                                               uu____3070
                                              in
                                           (match uu____3046 with
                                            | (t_body,guard_body) ->
                                                let k =
                                                  FStar_Syntax_Util.abs
                                                    (FStar_List.append bs
                                                       [f_bs; g_bs; p_b])
                                                    t_body
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
                                                 (let uu____3131 =
                                                    let uu____3134 =
                                                      FStar_All.pipe_right k
                                                        (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                           env)
                                                       in
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      conjunction_us
                                                      uu____3134
                                                     in
                                                  (conjunction_us,
                                                    uu____3131,
                                                    conjunction_ty)))))))))
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
                 (let uu____3166 =
                    let uu____3172 =
                      let uu____3174 =
                        FStar_Syntax_Print.binders_to_string "; "
                          act.FStar_Syntax_Syntax.action_params
                         in
                      FStar_Util.format3
                        "Action %s:%s has non-empty action params (%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                        (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                        uu____3174
                       in
                    (FStar_Errors.Fatal_MalformedActionDeclaration,
                      uu____3172)
                     in
                  FStar_Errors.raise_error uu____3166 r)
               else ();
               (let uu____3181 =
                  let uu____3186 =
                    FStar_Syntax_Subst.univ_var_opening
                      act.FStar_Syntax_Syntax.action_univs
                     in
                  match uu____3186 with
                  | (usubst,us) ->
                      let uu____3209 =
                        FStar_TypeChecker_Env.push_univ_vars env us  in
                      let uu____3210 =
                        let uu___317_3211 = act  in
                        let uu____3212 =
                          FStar_Syntax_Subst.subst usubst
                            act.FStar_Syntax_Syntax.action_defn
                           in
                        let uu____3213 =
                          FStar_Syntax_Subst.subst usubst
                            act.FStar_Syntax_Syntax.action_typ
                           in
                        {
                          FStar_Syntax_Syntax.action_name =
                            (uu___317_3211.FStar_Syntax_Syntax.action_name);
                          FStar_Syntax_Syntax.action_unqualified_name =
                            (uu___317_3211.FStar_Syntax_Syntax.action_unqualified_name);
                          FStar_Syntax_Syntax.action_univs = us;
                          FStar_Syntax_Syntax.action_params =
                            (uu___317_3211.FStar_Syntax_Syntax.action_params);
                          FStar_Syntax_Syntax.action_defn = uu____3212;
                          FStar_Syntax_Syntax.action_typ = uu____3213
                        }  in
                      (uu____3209, uu____3210)
                   in
                match uu____3181 with
                | (env1,act1) ->
                    let act_typ =
                      let uu____3217 =
                        let uu____3218 =
                          FStar_Syntax_Subst.compress
                            act1.FStar_Syntax_Syntax.action_typ
                           in
                        uu____3218.FStar_Syntax_Syntax.n  in
                      match uu____3217 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let ct = FStar_Syntax_Util.comp_to_comp_typ c  in
                          let uu____3244 =
                            FStar_Ident.lid_equals
                              ct.FStar_Syntax_Syntax.effect_name
                              ed.FStar_Syntax_Syntax.mname
                             in
                          if uu____3244
                          then
                            let repr_ts =
                              let uu____3248 = repr  in
                              match uu____3248 with
                              | (us,t,uu____3263) -> (us, t)  in
                            let repr1 =
                              let uu____3281 =
                                FStar_TypeChecker_Env.inst_tscheme_with
                                  repr_ts ct.FStar_Syntax_Syntax.comp_univs
                                 in
                              FStar_All.pipe_right uu____3281
                                FStar_Pervasives_Native.snd
                               in
                            let repr2 =
                              let uu____3293 =
                                let uu____3298 =
                                  let uu____3299 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ
                                     in
                                  uu____3299 ::
                                    (ct.FStar_Syntax_Syntax.effect_args)
                                   in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____3298
                                 in
                              uu____3293 FStar_Pervasives_Native.None r  in
                            let c1 =
                              let uu____3317 =
                                let uu____3320 =
                                  FStar_TypeChecker_Env.new_u_univ ()  in
                                FStar_Pervasives_Native.Some uu____3320  in
                              FStar_Syntax_Syntax.mk_Total' repr2 uu____3317
                               in
                            FStar_Syntax_Util.arrow bs c1
                          else act1.FStar_Syntax_Syntax.action_typ
                      | uu____3323 -> act1.FStar_Syntax_Syntax.action_typ  in
                    let uu____3324 =
                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                        act_typ
                       in
                    (match uu____3324 with
                     | (act_typ1,uu____3332,g_t) ->
                         let uu____3334 =
                           let uu____3341 =
                             let uu___342_3342 =
                               FStar_TypeChecker_Env.set_expected_typ env1
                                 act_typ1
                                in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___342_3342.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___342_3342.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___342_3342.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___342_3342.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___342_3342.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___342_3342.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___342_3342.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___342_3342.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___342_3342.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___342_3342.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___342_3342.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp = false;
                               FStar_TypeChecker_Env.effects =
                                 (uu___342_3342.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___342_3342.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___342_3342.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___342_3342.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___342_3342.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___342_3342.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___342_3342.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___342_3342.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___342_3342.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___342_3342.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___342_3342.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___342_3342.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___342_3342.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___342_3342.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___342_3342.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___342_3342.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___342_3342.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___342_3342.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___342_3342.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___342_3342.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___342_3342.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___342_3342.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___342_3342.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___342_3342.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___342_3342.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___342_3342.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___342_3342.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___342_3342.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___342_3342.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___342_3342.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___342_3342.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___342_3342.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___342_3342.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___342_3342.FStar_TypeChecker_Env.erasable_types_tab)
                             }  in
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                             uu____3341 act1.FStar_Syntax_Syntax.action_defn
                            in
                         (match uu____3334 with
                          | (act_defn,uu____3345,g_d) ->
                              ((let uu____3348 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env1)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____3348
                                then
                                  let uu____3353 =
                                    FStar_Syntax_Print.term_to_string
                                      act_defn
                                     in
                                  let uu____3355 =
                                    FStar_Syntax_Print.term_to_string
                                      act_typ1
                                     in
                                  FStar_Util.print2
                                    "Typechecked action definition: %s and action type: %s\n"
                                    uu____3353 uu____3355
                                else ());
                               (let uu____3360 =
                                  let act_typ2 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Beta] env1
                                      act_typ1
                                     in
                                  let uu____3368 =
                                    let uu____3369 =
                                      FStar_Syntax_Subst.compress act_typ2
                                       in
                                    uu____3369.FStar_Syntax_Syntax.n  in
                                  match uu____3368 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____3379) ->
                                      let bs1 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      let env2 =
                                        FStar_TypeChecker_Env.push_binders
                                          env1 bs1
                                         in
                                      let uu____3402 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____3402 with
                                       | (t,u) ->
                                           let reason =
                                             FStar_Util.format2
                                               "implicit for return type of action %s:%s"
                                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                              in
                                           let uu____3418 =
                                             FStar_TypeChecker_Util.new_implicit_var
                                               reason r env2 t
                                              in
                                           (match uu____3418 with
                                            | (a_tm,uu____3438,g_tm) ->
                                                let uu____3452 =
                                                  fresh_repr r env2 u a_tm
                                                   in
                                                (match uu____3452 with
                                                 | (repr1,g) ->
                                                     let uu____3465 =
                                                       let uu____3468 =
                                                         let uu____3471 =
                                                           let uu____3474 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____3474
                                                             (fun _3477  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _3477)
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____3471
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         bs1 uu____3468
                                                        in
                                                     let uu____3478 =
                                                       FStar_TypeChecker_Env.conj_guard
                                                         g g_tm
                                                        in
                                                     (uu____3465, uu____3478))))
                                  | uu____3481 ->
                                      let uu____3482 =
                                        let uu____3488 =
                                          let uu____3490 =
                                            FStar_Syntax_Print.term_to_string
                                              act_typ2
                                             in
                                          FStar_Util.format3
                                            "Unexpected non-function type for action %s:%s (%s)"
                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                            (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                            uu____3490
                                           in
                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                          uu____3488)
                                         in
                                      FStar_Errors.raise_error uu____3482 r
                                   in
                                match uu____3360 with
                                | (k,g_k) ->
                                    ((let uu____3507 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____3507
                                      then
                                        let uu____3512 =
                                          FStar_Syntax_Print.term_to_string k
                                           in
                                        FStar_Util.print1
                                          "Expected action type: %s\n"
                                          uu____3512
                                      else ());
                                     (let g =
                                        FStar_TypeChecker_Rel.teq env1
                                          act_typ1 k
                                         in
                                      FStar_List.iter
                                        (FStar_TypeChecker_Rel.force_trivial_guard
                                           env1) [g_t; g_d; g_k; g];
                                      (let uu____3520 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3520
                                       then
                                         let uu____3525 =
                                           FStar_Syntax_Print.term_to_string
                                             k
                                            in
                                         FStar_Util.print1
                                           "Expected action type after unification: %s\n"
                                           uu____3525
                                       else ());
                                      (let act_typ2 =
                                         let err_msg t =
                                           let uu____3538 =
                                             FStar_Syntax_Print.term_to_string
                                               t
                                              in
                                           FStar_Util.format3
                                             "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                             (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                             (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                             uu____3538
                                            in
                                         let repr_args t =
                                           let uu____3559 =
                                             let uu____3560 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____3560.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3559 with
                                           | FStar_Syntax_Syntax.Tm_app
                                               (head1,a::is) ->
                                               let uu____3612 =
                                                 let uu____3613 =
                                                   FStar_Syntax_Subst.compress
                                                     head1
                                                    in
                                                 uu____3613.FStar_Syntax_Syntax.n
                                                  in
                                               (match uu____3612 with
                                                | FStar_Syntax_Syntax.Tm_uinst
                                                    (uu____3622,us) ->
                                                    (us,
                                                      (FStar_Pervasives_Native.fst
                                                         a), is)
                                                | uu____3632 ->
                                                    let uu____3633 =
                                                      let uu____3639 =
                                                        err_msg t  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____3639)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3633 r)
                                           | uu____3648 ->
                                               let uu____3649 =
                                                 let uu____3655 = err_msg t
                                                    in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____3655)
                                                  in
                                               FStar_Errors.raise_error
                                                 uu____3649 r
                                            in
                                         let k1 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 k
                                            in
                                         let uu____3665 =
                                           let uu____3666 =
                                             FStar_Syntax_Subst.compress k1
                                              in
                                           uu____3666.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3665 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,c) ->
                                             let uu____3691 =
                                               FStar_Syntax_Subst.open_comp
                                                 bs c
                                                in
                                             (match uu____3691 with
                                              | (bs1,c1) ->
                                                  let uu____3698 =
                                                    repr_args
                                                      (FStar_Syntax_Util.comp_result
                                                         c1)
                                                     in
                                                  (match uu____3698 with
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
                                                       let uu____3709 =
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           ct
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         bs1 uu____3709))
                                         | uu____3712 ->
                                             let uu____3713 =
                                               let uu____3719 = err_msg k1
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____3719)
                                                in
                                             FStar_Errors.raise_error
                                               uu____3713 r
                                          in
                                       (let uu____3723 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffects")
                                           in
                                        if uu____3723
                                        then
                                          let uu____3728 =
                                            FStar_Syntax_Print.term_to_string
                                              act_typ2
                                             in
                                          FStar_Util.print1
                                            "Action type after injecting it into the monad: %s\n"
                                            uu____3728
                                        else ());
                                       (let act2 =
                                          let uu____3734 =
                                            FStar_TypeChecker_Util.generalize_universes
                                              env1 act_defn
                                             in
                                          match uu____3734 with
                                          | (us,act_defn1) ->
                                              if
                                                act1.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then
                                                let uu___415_3748 = act1  in
                                                let uu____3749 =
                                                  FStar_Syntax_Subst.close_univ_vars
                                                    us act_typ2
                                                   in
                                                {
                                                  FStar_Syntax_Syntax.action_name
                                                    =
                                                    (uu___415_3748.FStar_Syntax_Syntax.action_name);
                                                  FStar_Syntax_Syntax.action_unqualified_name
                                                    =
                                                    (uu___415_3748.FStar_Syntax_Syntax.action_unqualified_name);
                                                  FStar_Syntax_Syntax.action_univs
                                                    = us;
                                                  FStar_Syntax_Syntax.action_params
                                                    =
                                                    (uu___415_3748.FStar_Syntax_Syntax.action_params);
                                                  FStar_Syntax_Syntax.action_defn
                                                    = act_defn1;
                                                  FStar_Syntax_Syntax.action_typ
                                                    = uu____3749
                                                }
                                              else
                                                (let uu____3752 =
                                                   ((FStar_List.length us) =
                                                      (FStar_List.length
                                                         act1.FStar_Syntax_Syntax.action_univs))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1  ->
                                                           fun u2  ->
                                                             let uu____3759 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2
                                                                in
                                                             uu____3759 =
                                                               Prims.int_zero)
                                                        us
                                                        act1.FStar_Syntax_Syntax.action_univs)
                                                    in
                                                 if uu____3752
                                                 then
                                                   let uu___420_3764 = act1
                                                      in
                                                   let uu____3765 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                       act_typ2
                                                      in
                                                   {
                                                     FStar_Syntax_Syntax.action_name
                                                       =
                                                       (uu___420_3764.FStar_Syntax_Syntax.action_name);
                                                     FStar_Syntax_Syntax.action_unqualified_name
                                                       =
                                                       (uu___420_3764.FStar_Syntax_Syntax.action_unqualified_name);
                                                     FStar_Syntax_Syntax.action_univs
                                                       =
                                                       (uu___420_3764.FStar_Syntax_Syntax.action_univs);
                                                     FStar_Syntax_Syntax.action_params
                                                       =
                                                       (uu___420_3764.FStar_Syntax_Syntax.action_params);
                                                     FStar_Syntax_Syntax.action_defn
                                                       = act_defn1;
                                                     FStar_Syntax_Syntax.action_typ
                                                       = uu____3765
                                                   }
                                                 else
                                                   (let uu____3768 =
                                                      let uu____3774 =
                                                        let uu____3776 =
                                                          FStar_Syntax_Print.univ_names_to_string
                                                            us
                                                           in
                                                        let uu____3778 =
                                                          FStar_Syntax_Print.univ_names_to_string
                                                            act1.FStar_Syntax_Syntax.action_univs
                                                           in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                          (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                          (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                          uu____3776
                                                          uu____3778
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____3774)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3768 r))
                                           in
                                        act2)))))))))
                in
             let fst1 uu____3801 =
               match uu____3801 with | (a,uu____3817,uu____3818) -> a  in
             let snd1 uu____3850 =
               match uu____3850 with | (uu____3865,b,uu____3867) -> b  in
             let thd uu____3899 =
               match uu____3899 with | (uu____3914,uu____3915,c) -> c  in
             let uu___438_3929 = ed  in
             let uu____3930 =
               FStar_All.pipe_right
                 ((fst1 stronger_repr), (snd1 stronger_repr))
                 (fun _3939  -> FStar_Pervasives_Native.Some _3939)
                in
             let uu____3940 =
               FStar_List.map (tc_action env0) ed.FStar_Syntax_Syntax.actions
                in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___438_3929.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___438_3929.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___438_3929.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs =
                 (uu___438_3929.FStar_Syntax_Syntax.univs);
               FStar_Syntax_Syntax.binders =
                 (uu___438_3929.FStar_Syntax_Syntax.binders);
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
                 (uu___438_3929.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
               FStar_Syntax_Syntax.return_repr =
                 ((fst1 return_repr), (snd1 return_repr));
               FStar_Syntax_Syntax.bind_repr =
                 ((fst1 bind_repr), (snd1 bind_repr));
               FStar_Syntax_Syntax.stronger_repr = uu____3930;
               FStar_Syntax_Syntax.actions = uu____3940;
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___438_3929.FStar_Syntax_Syntax.eff_attrs)
             })))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____3991 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____3991 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4018 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____4018
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      (let uu____4031 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "ED")
          in
       if uu____4031
       then
         let uu____4036 = FStar_Syntax_Print.eff_decl_to_string false ed  in
         FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4036
       else ());
      (let uu____4042 =
         let uu____4047 =
           FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
            in
         match uu____4047 with
         | (ed_univs_subst,ed_univs) ->
             let bs =
               let uu____4071 =
                 FStar_Syntax_Subst.subst_binders ed_univs_subst
                   ed.FStar_Syntax_Syntax.binders
                  in
               FStar_Syntax_Subst.open_binders uu____4071  in
             let uu____4072 =
               let uu____4079 =
                 FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
               FStar_TypeChecker_TcTerm.tc_tparams uu____4079 bs  in
             (match uu____4072 with
              | (bs1,uu____4085,uu____4086) ->
                  let uu____4087 =
                    let tmp_t =
                      let uu____4097 =
                        let uu____4100 =
                          FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                            (fun _4105  -> FStar_Pervasives_Native.Some _4105)
                           in
                        FStar_Syntax_Syntax.mk_Total'
                          FStar_Syntax_Syntax.t_unit uu____4100
                         in
                      FStar_Syntax_Util.arrow bs1 uu____4097  in
                    let uu____4106 =
                      FStar_TypeChecker_Util.generalize_universes env0 tmp_t
                       in
                    match uu____4106 with
                    | (us,tmp_t1) ->
                        let uu____4123 =
                          let uu____4124 =
                            let uu____4125 =
                              FStar_All.pipe_right tmp_t1
                                FStar_Syntax_Util.arrow_formals
                               in
                            FStar_All.pipe_right uu____4125
                              FStar_Pervasives_Native.fst
                             in
                          FStar_All.pipe_right uu____4124
                            FStar_Syntax_Subst.close_binders
                           in
                        (us, uu____4123)
                     in
                  (match uu____4087 with
                   | (us,bs2) ->
                       (match ed_univs with
                        | [] -> (us, bs2)
                        | uu____4194 ->
                            let uu____4197 =
                              ((FStar_List.length ed_univs) =
                                 (FStar_List.length us))
                                &&
                                (FStar_List.forall2
                                   (fun u1  ->
                                      fun u2  ->
                                        let uu____4204 =
                                          FStar_Syntax_Syntax.order_univ_name
                                            u1 u2
                                           in
                                        uu____4204 = Prims.int_zero) ed_univs
                                   us)
                               in
                            if uu____4197
                            then (us, bs2)
                            else
                              (let uu____4215 =
                                 let uu____4221 =
                                   let uu____4223 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length ed_univs)
                                      in
                                   let uu____4225 =
                                     FStar_Util.string_of_int
                                       (FStar_List.length us)
                                      in
                                   FStar_Util.format3
                                     "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                     uu____4223 uu____4225
                                    in
                                 (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                   uu____4221)
                                  in
                               let uu____4229 =
                                 FStar_Ident.range_of_lid
                                   ed.FStar_Syntax_Syntax.mname
                                  in
                               FStar_Errors.raise_error uu____4215 uu____4229))))
          in
       match uu____4042 with
       | (us,bs) ->
           let ed1 =
             let uu___478_4237 = ed  in
             {
               FStar_Syntax_Syntax.is_layered =
                 (uu___478_4237.FStar_Syntax_Syntax.is_layered);
               FStar_Syntax_Syntax.cattributes =
                 (uu___478_4237.FStar_Syntax_Syntax.cattributes);
               FStar_Syntax_Syntax.mname =
                 (uu___478_4237.FStar_Syntax_Syntax.mname);
               FStar_Syntax_Syntax.univs = us;
               FStar_Syntax_Syntax.binders = bs;
               FStar_Syntax_Syntax.signature =
                 (uu___478_4237.FStar_Syntax_Syntax.signature);
               FStar_Syntax_Syntax.ret_wp =
                 (uu___478_4237.FStar_Syntax_Syntax.ret_wp);
               FStar_Syntax_Syntax.bind_wp =
                 (uu___478_4237.FStar_Syntax_Syntax.bind_wp);
               FStar_Syntax_Syntax.stronger =
                 (uu___478_4237.FStar_Syntax_Syntax.stronger);
               FStar_Syntax_Syntax.match_wps =
                 (uu___478_4237.FStar_Syntax_Syntax.match_wps);
               FStar_Syntax_Syntax.trivial =
                 (uu___478_4237.FStar_Syntax_Syntax.trivial);
               FStar_Syntax_Syntax.repr =
                 (uu___478_4237.FStar_Syntax_Syntax.repr);
               FStar_Syntax_Syntax.return_repr =
                 (uu___478_4237.FStar_Syntax_Syntax.return_repr);
               FStar_Syntax_Syntax.bind_repr =
                 (uu___478_4237.FStar_Syntax_Syntax.bind_repr);
               FStar_Syntax_Syntax.stronger_repr =
                 (uu___478_4237.FStar_Syntax_Syntax.stronger_repr);
               FStar_Syntax_Syntax.actions =
                 (uu___478_4237.FStar_Syntax_Syntax.actions);
               FStar_Syntax_Syntax.eff_attrs =
                 (uu___478_4237.FStar_Syntax_Syntax.eff_attrs)
             }  in
           let uu____4238 = FStar_Syntax_Subst.univ_var_opening us  in
           (match uu____4238 with
            | (ed_univs_subst,ed_univs) ->
                let uu____4257 =
                  let uu____4262 =
                    FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                  FStar_Syntax_Subst.open_binders' uu____4262  in
                (match uu____4257 with
                 | (ed_bs,ed_bs_subst) ->
                     let ed2 =
                       let op uu____4283 =
                         match uu____4283 with
                         | (us1,t) ->
                             let t1 =
                               let uu____4303 =
                                 FStar_Syntax_Subst.shift_subst
                                   ((FStar_List.length ed_bs) +
                                      (FStar_List.length us1)) ed_univs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4303 t  in
                             let uu____4312 =
                               let uu____4313 =
                                 FStar_Syntax_Subst.shift_subst
                                   (FStar_List.length us1) ed_bs_subst
                                  in
                               FStar_Syntax_Subst.subst uu____4313 t1  in
                             (us1, uu____4312)
                          in
                       let uu___492_4318 = ed1  in
                       let uu____4319 = op ed1.FStar_Syntax_Syntax.signature
                          in
                       let uu____4320 = op ed1.FStar_Syntax_Syntax.ret_wp  in
                       let uu____4321 = op ed1.FStar_Syntax_Syntax.bind_wp
                          in
                       let uu____4322 = op ed1.FStar_Syntax_Syntax.stronger
                          in
                       let uu____4323 =
                         FStar_Syntax_Util.map_match_wps op
                           ed1.FStar_Syntax_Syntax.match_wps
                          in
                       let uu____4328 =
                         FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                           op
                          in
                       let uu____4331 = op ed1.FStar_Syntax_Syntax.repr  in
                       let uu____4332 =
                         op ed1.FStar_Syntax_Syntax.return_repr  in
                       let uu____4333 = op ed1.FStar_Syntax_Syntax.bind_repr
                          in
                       let uu____4334 =
                         FStar_List.map
                           (fun a  ->
                              let uu___495_4342 = a  in
                              let uu____4343 =
                                let uu____4344 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_defn))
                                   in
                                FStar_Pervasives_Native.snd uu____4344  in
                              let uu____4355 =
                                let uu____4356 =
                                  op
                                    ((a.FStar_Syntax_Syntax.action_univs),
                                      (a.FStar_Syntax_Syntax.action_typ))
                                   in
                                FStar_Pervasives_Native.snd uu____4356  in
                              {
                                FStar_Syntax_Syntax.action_name =
                                  (uu___495_4342.FStar_Syntax_Syntax.action_name);
                                FStar_Syntax_Syntax.action_unqualified_name =
                                  (uu___495_4342.FStar_Syntax_Syntax.action_unqualified_name);
                                FStar_Syntax_Syntax.action_univs =
                                  (uu___495_4342.FStar_Syntax_Syntax.action_univs);
                                FStar_Syntax_Syntax.action_params =
                                  (uu___495_4342.FStar_Syntax_Syntax.action_params);
                                FStar_Syntax_Syntax.action_defn = uu____4343;
                                FStar_Syntax_Syntax.action_typ = uu____4355
                              }) ed1.FStar_Syntax_Syntax.actions
                          in
                       {
                         FStar_Syntax_Syntax.is_layered =
                           (uu___492_4318.FStar_Syntax_Syntax.is_layered);
                         FStar_Syntax_Syntax.cattributes =
                           (uu___492_4318.FStar_Syntax_Syntax.cattributes);
                         FStar_Syntax_Syntax.mname =
                           (uu___492_4318.FStar_Syntax_Syntax.mname);
                         FStar_Syntax_Syntax.univs =
                           (uu___492_4318.FStar_Syntax_Syntax.univs);
                         FStar_Syntax_Syntax.binders =
                           (uu___492_4318.FStar_Syntax_Syntax.binders);
                         FStar_Syntax_Syntax.signature = uu____4319;
                         FStar_Syntax_Syntax.ret_wp = uu____4320;
                         FStar_Syntax_Syntax.bind_wp = uu____4321;
                         FStar_Syntax_Syntax.stronger = uu____4322;
                         FStar_Syntax_Syntax.match_wps = uu____4323;
                         FStar_Syntax_Syntax.trivial = uu____4328;
                         FStar_Syntax_Syntax.repr = uu____4331;
                         FStar_Syntax_Syntax.return_repr = uu____4332;
                         FStar_Syntax_Syntax.bind_repr = uu____4333;
                         FStar_Syntax_Syntax.stronger_repr =
                           FStar_Pervasives_Native.None;
                         FStar_Syntax_Syntax.actions = uu____4334;
                         FStar_Syntax_Syntax.eff_attrs =
                           (uu___492_4318.FStar_Syntax_Syntax.eff_attrs)
                       }  in
                     ((let uu____4368 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "ED")
                          in
                       if uu____4368
                       then
                         let uu____4373 =
                           FStar_Syntax_Print.eff_decl_to_string false ed2
                            in
                         FStar_Util.print1
                           "After typechecking binders eff_decl: \n\t%s\n"
                           uu____4373
                       else ());
                      (let env =
                         let uu____4380 =
                           FStar_TypeChecker_Env.push_univ_vars env0 ed_univs
                            in
                         FStar_TypeChecker_Env.push_binders uu____4380 ed_bs
                          in
                       let check_and_gen' comb n1 env_opt uu____4415 k =
                         match uu____4415 with
                         | (us1,t) ->
                             let env1 =
                               if FStar_Util.is_some env_opt
                               then
                                 FStar_All.pipe_right env_opt FStar_Util.must
                               else env  in
                             let uu____4435 =
                               FStar_Syntax_Subst.open_univ_vars us1 t  in
                             (match uu____4435 with
                              | (us2,t1) ->
                                  let t2 =
                                    match k with
                                    | FStar_Pervasives_Native.Some k1 ->
                                        let uu____4444 =
                                          FStar_TypeChecker_Env.push_univ_vars
                                            env1 us2
                                           in
                                        tc_check_trivial_guard uu____4444 t1
                                          k1
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____4445 =
                                          let uu____4452 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                            uu____4452 t1
                                           in
                                        (match uu____4445 with
                                         | (t2,uu____4454,g) ->
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env1 g;
                                              t2))
                                     in
                                  let uu____4457 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env1 t2
                                     in
                                  (match uu____4457 with
                                   | (g_us,t3) ->
                                       (if (FStar_List.length g_us) <> n1
                                        then
                                          (let error =
                                             let uu____4473 =
                                               FStar_Util.string_of_int n1
                                                in
                                             let uu____4475 =
                                               let uu____4477 =
                                                 FStar_All.pipe_right g_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____4477
                                                 FStar_Util.string_of_int
                                                in
                                             FStar_Util.format4
                                               "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                               (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                               comb uu____4473 uu____4475
                                              in
                                           FStar_Errors.raise_error
                                             (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                               error)
                                             t3.FStar_Syntax_Syntax.pos)
                                        else ();
                                        (match us2 with
                                         | [] -> (g_us, t3)
                                         | uu____4492 ->
                                             let uu____4493 =
                                               ((FStar_List.length us2) =
                                                  (FStar_List.length g_us))
                                                 &&
                                                 (FStar_List.forall2
                                                    (fun u1  ->
                                                       fun u2  ->
                                                         let uu____4500 =
                                                           FStar_Syntax_Syntax.order_univ_name
                                                             u1 u2
                                                            in
                                                         uu____4500 =
                                                           Prims.int_zero)
                                                    us2 g_us)
                                                in
                                             if uu____4493
                                             then (g_us, t3)
                                             else
                                               (let uu____4511 =
                                                  let uu____4517 =
                                                    let uu____4519 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           us2)
                                                       in
                                                    let uu____4521 =
                                                      FStar_Util.string_of_int
                                                        (FStar_List.length
                                                           g_us)
                                                       in
                                                    FStar_Util.format4
                                                      "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                      (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      comb uu____4519
                                                      uu____4521
                                                     in
                                                  (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                    uu____4517)
                                                   in
                                                FStar_Errors.raise_error
                                                  uu____4511
                                                  t3.FStar_Syntax_Syntax.pos)))))
                          in
                       let signature =
                         check_and_gen' "signature" Prims.int_one
                           FStar_Pervasives_Native.None
                           ed2.FStar_Syntax_Syntax.signature
                           FStar_Pervasives_Native.None
                          in
                       (let uu____4529 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "ED")
                           in
                        if uu____4529
                        then
                          let uu____4534 =
                            FStar_Syntax_Print.tscheme_to_string signature
                             in
                          FStar_Util.print1 "Typechecked signature: %s\n"
                            uu____4534
                        else ());
                       (let fresh_a_and_wp uu____4550 =
                          let fail1 t =
                            let uu____4563 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env ed2.FStar_Syntax_Syntax.mname t
                               in
                            FStar_Errors.raise_error uu____4563
                              (FStar_Pervasives_Native.snd
                                 ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                             in
                          let uu____4579 =
                            FStar_TypeChecker_Env.inst_tscheme signature  in
                          match uu____4579 with
                          | (uu____4590,signature1) ->
                              let uu____4592 =
                                let uu____4593 =
                                  FStar_Syntax_Subst.compress signature1  in
                                uu____4593.FStar_Syntax_Syntax.n  in
                              (match uu____4592 with
                               | FStar_Syntax_Syntax.Tm_arrow
                                   (bs1,uu____4603) ->
                                   let bs2 =
                                     FStar_Syntax_Subst.open_binders bs1  in
                                   (match bs2 with
                                    | (a,uu____4632)::(wp,uu____4634)::[] ->
                                        (a, (wp.FStar_Syntax_Syntax.sort))
                                    | uu____4663 -> fail1 signature1)
                               | uu____4664 -> fail1 signature1)
                           in
                        let log_combinator s ts =
                          let uu____4678 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4678
                          then
                            let uu____4683 =
                              FStar_Syntax_Print.tscheme_to_string ts  in
                            FStar_Util.print3 "Typechecked %s:%s = %s\n"
                              (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                              s uu____4683
                          else ()  in
                        let ret_wp =
                          let uu____4689 = fresh_a_and_wp ()  in
                          match uu____4689 with
                          | (a,wp_sort) ->
                              let k =
                                let uu____4705 =
                                  let uu____4714 =
                                    FStar_Syntax_Syntax.mk_binder a  in
                                  let uu____4721 =
                                    let uu____4730 =
                                      let uu____4737 =
                                        FStar_Syntax_Syntax.bv_to_name a  in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4737
                                       in
                                    [uu____4730]  in
                                  uu____4714 :: uu____4721  in
                                let uu____4756 =
                                  FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                FStar_Syntax_Util.arrow uu____4705 uu____4756
                                 in
                              check_and_gen' "ret_wp" Prims.int_one
                                FStar_Pervasives_Native.None
                                ed2.FStar_Syntax_Syntax.ret_wp
                                (FStar_Pervasives_Native.Some k)
                           in
                        log_combinator "ret_wp" ret_wp;
                        (let bind_wp =
                           let uu____4764 = fresh_a_and_wp ()  in
                           match uu____4764 with
                           | (a,wp_sort_a) ->
                               let uu____4777 = fresh_a_and_wp ()  in
                               (match uu____4777 with
                                | (b,wp_sort_b) ->
                                    let wp_sort_a_b =
                                      let uu____4793 =
                                        let uu____4802 =
                                          let uu____4809 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____4809
                                           in
                                        [uu____4802]  in
                                      let uu____4822 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4793
                                        uu____4822
                                       in
                                    let k =
                                      let uu____4828 =
                                        let uu____4837 =
                                          FStar_Syntax_Syntax.null_binder
                                            FStar_Syntax_Syntax.t_range
                                           in
                                        let uu____4844 =
                                          let uu____4853 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____4860 =
                                            let uu____4869 =
                                              FStar_Syntax_Syntax.mk_binder b
                                               in
                                            let uu____4876 =
                                              let uu____4885 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              let uu____4892 =
                                                let uu____4901 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a_b
                                                   in
                                                [uu____4901]  in
                                              uu____4885 :: uu____4892  in
                                            uu____4869 :: uu____4876  in
                                          uu____4853 :: uu____4860  in
                                        uu____4837 :: uu____4844  in
                                      let uu____4944 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_b
                                         in
                                      FStar_Syntax_Util.arrow uu____4828
                                        uu____4944
                                       in
                                    check_and_gen' "bind_wp"
                                      (Prims.of_int (2))
                                      FStar_Pervasives_Native.None
                                      ed2.FStar_Syntax_Syntax.bind_wp
                                      (FStar_Pervasives_Native.Some k))
                            in
                         log_combinator "bind_wp" bind_wp;
                         (let stronger =
                            let uu____4952 = fresh_a_and_wp ()  in
                            match uu____4952 with
                            | (a,wp_sort_a) ->
                                let uu____4965 = FStar_Syntax_Util.type_u ()
                                   in
                                (match uu____4965 with
                                 | (t,uu____4971) ->
                                     let k =
                                       let uu____4975 =
                                         let uu____4984 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____4991 =
                                           let uu____5000 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____5007 =
                                             let uu____5016 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____5016]  in
                                           uu____5000 :: uu____5007  in
                                         uu____4984 :: uu____4991  in
                                       let uu____5047 =
                                         FStar_Syntax_Syntax.mk_Total t  in
                                       FStar_Syntax_Util.arrow uu____4975
                                         uu____5047
                                        in
                                     check_and_gen' "stronger" Prims.int_one
                                       FStar_Pervasives_Native.None
                                       ed2.FStar_Syntax_Syntax.stronger
                                       (FStar_Pervasives_Native.Some k))
                             in
                          log_combinator "stronger" stronger;
                          (let match_wps =
                             let uu____5059 =
                               FStar_Syntax_Util.get_match_with_close_wps
                                 ed2.FStar_Syntax_Syntax.match_wps
                                in
                             match uu____5059 with
                             | (if_then_else1,ite_wp,close_wp) ->
                                 let if_then_else2 =
                                   let uu____5074 = fresh_a_and_wp ()  in
                                   match uu____5074 with
                                   | (a,wp_sort_a) ->
                                       let p =
                                         let uu____5088 =
                                           let uu____5091 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____5091
                                            in
                                         let uu____5092 =
                                           let uu____5093 =
                                             FStar_Syntax_Util.type_u ()  in
                                           FStar_All.pipe_right uu____5093
                                             FStar_Pervasives_Native.fst
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____5088 uu____5092
                                          in
                                       let k =
                                         let uu____5105 =
                                           let uu____5114 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5121 =
                                             let uu____5130 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 p
                                                in
                                             let uu____5137 =
                                               let uu____5146 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               let uu____5153 =
                                                 let uu____5162 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5162]  in
                                               uu____5146 :: uu____5153  in
                                             uu____5130 :: uu____5137  in
                                           uu____5114 :: uu____5121  in
                                         let uu____5199 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a
                                            in
                                         FStar_Syntax_Util.arrow uu____5105
                                           uu____5199
                                          in
                                       check_and_gen' "if_then_else"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         if_then_else1
                                         (FStar_Pervasives_Native.Some k)
                                    in
                                 (log_combinator "if_then_else" if_then_else2;
                                  (let ite_wp1 =
                                     let uu____5207 = fresh_a_and_wp ()  in
                                     match uu____5207 with
                                     | (a,wp_sort_a) ->
                                         let k =
                                           let uu____5223 =
                                             let uu____5232 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5239 =
                                               let uu____5248 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5248]  in
                                             uu____5232 :: uu____5239  in
                                           let uu____5273 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5223
                                             uu____5273
                                            in
                                         check_and_gen' "ite_wp"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           ite_wp
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   log_combinator "ite_wp" ite_wp1;
                                   (let close_wp1 =
                                      let uu____5281 = fresh_a_and_wp ()  in
                                      match uu____5281 with
                                      | (a,wp_sort_a) ->
                                          let b =
                                            let uu____5295 =
                                              let uu____5298 =
                                                FStar_Ident.range_of_lid
                                                  ed2.FStar_Syntax_Syntax.mname
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____5298
                                               in
                                            let uu____5299 =
                                              let uu____5300 =
                                                FStar_Syntax_Util.type_u ()
                                                 in
                                              FStar_All.pipe_right uu____5300
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_Syntax_Syntax.new_bv
                                              uu____5295 uu____5299
                                             in
                                          let wp_sort_b_a =
                                            let uu____5312 =
                                              let uu____5321 =
                                                let uu____5328 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    b
                                                   in
                                                FStar_Syntax_Syntax.null_binder
                                                  uu____5328
                                                 in
                                              [uu____5321]  in
                                            let uu____5341 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5312 uu____5341
                                             in
                                          let k =
                                            let uu____5347 =
                                              let uu____5356 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a
                                                 in
                                              let uu____5363 =
                                                let uu____5372 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b
                                                   in
                                                let uu____5379 =
                                                  let uu____5388 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_b_a
                                                     in
                                                  [uu____5388]  in
                                                uu____5372 :: uu____5379  in
                                              uu____5356 :: uu____5363  in
                                            let uu____5419 =
                                              FStar_Syntax_Syntax.mk_Total
                                                wp_sort_a
                                               in
                                            FStar_Syntax_Util.arrow
                                              uu____5347 uu____5419
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
                             let uu____5429 = fresh_a_and_wp ()  in
                             match uu____5429 with
                             | (a,wp_sort_a) ->
                                 let uu____5444 = FStar_Syntax_Util.type_u ()
                                    in
                                 (match uu____5444 with
                                  | (t,uu____5452) ->
                                      let k =
                                        let uu____5456 =
                                          let uu____5465 =
                                            FStar_Syntax_Syntax.mk_binder a
                                             in
                                          let uu____5472 =
                                            let uu____5481 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a
                                               in
                                            [uu____5481]  in
                                          uu____5465 :: uu____5472  in
                                        let uu____5506 =
                                          FStar_Syntax_Syntax.mk_GTotal t  in
                                        FStar_Syntax_Util.arrow uu____5456
                                          uu____5506
                                         in
                                      let trivial =
                                        let uu____5510 =
                                          FStar_All.pipe_right
                                            ed2.FStar_Syntax_Syntax.trivial
                                            FStar_Util.must
                                           in
                                        check_and_gen' "trivial"
                                          Prims.int_one
                                          FStar_Pervasives_Native.None
                                          uu____5510
                                          (FStar_Pervasives_Native.Some k)
                                         in
                                      (log_combinator "trivial" trivial;
                                       FStar_Pervasives_Native.Some trivial))
                              in
                           let uu____5525 =
                             let uu____5536 =
                               let uu____5537 =
                                 FStar_Syntax_Subst.compress
                                   (FStar_Pervasives_Native.snd
                                      ed2.FStar_Syntax_Syntax.repr)
                                  in
                               uu____5537.FStar_Syntax_Syntax.n  in
                             match uu____5536 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____5556 ->
                                 let repr =
                                   let uu____5558 = fresh_a_and_wp ()  in
                                   match uu____5558 with
                                   | (a,wp_sort_a) ->
                                       let uu____5571 =
                                         FStar_Syntax_Util.type_u ()  in
                                       (match uu____5571 with
                                        | (t,uu____5577) ->
                                            let k =
                                              let uu____5581 =
                                                let uu____5590 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5597 =
                                                  let uu____5606 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a
                                                     in
                                                  [uu____5606]  in
                                                uu____5590 :: uu____5597  in
                                              let uu____5631 =
                                                FStar_Syntax_Syntax.mk_GTotal
                                                  t
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5581 uu____5631
                                               in
                                            check_and_gen' "repr"
                                              Prims.int_one
                                              FStar_Pervasives_Native.None
                                              ed2.FStar_Syntax_Syntax.repr
                                              (FStar_Pervasives_Native.Some k))
                                    in
                                 (log_combinator "repr" repr;
                                  (let mk_repr' t wp =
                                     let uu____5651 =
                                       FStar_TypeChecker_Env.inst_tscheme
                                         repr
                                        in
                                     match uu____5651 with
                                     | (uu____5658,repr1) ->
                                         let repr2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.EraseUniverses;
                                             FStar_TypeChecker_Env.AllowUnboundUniverses]
                                             env repr1
                                            in
                                         let uu____5661 =
                                           let uu____5668 =
                                             let uu____5669 =
                                               let uu____5686 =
                                                 let uu____5697 =
                                                   FStar_All.pipe_right t
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5714 =
                                                   let uu____5725 =
                                                     FStar_All.pipe_right wp
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5725]  in
                                                 uu____5697 :: uu____5714  in
                                               (repr2, uu____5686)  in
                                             FStar_Syntax_Syntax.Tm_app
                                               uu____5669
                                              in
                                           FStar_Syntax_Syntax.mk uu____5668
                                            in
                                         uu____5661
                                           FStar_Pervasives_Native.None
                                           FStar_Range.dummyRange
                                      in
                                   let mk_repr a wp =
                                     let uu____5791 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     mk_repr' uu____5791 wp  in
                                   let destruct_repr t =
                                     let uu____5806 =
                                       let uu____5807 =
                                         FStar_Syntax_Subst.compress t  in
                                       uu____5807.FStar_Syntax_Syntax.n  in
                                     match uu____5806 with
                                     | FStar_Syntax_Syntax.Tm_app
                                         (uu____5818,(t1,uu____5820)::
                                          (wp,uu____5822)::[])
                                         -> (t1, wp)
                                     | uu____5881 ->
                                         failwith "Unexpected repr type"
                                      in
                                   let return_repr =
                                     let uu____5892 = fresh_a_and_wp ()  in
                                     match uu____5892 with
                                     | (a,uu____5900) ->
                                         let x_a =
                                           let uu____5906 =
                                             FStar_Syntax_Syntax.bv_to_name a
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x_a"
                                             FStar_Pervasives_Native.None
                                             uu____5906
                                            in
                                         let res =
                                           let wp =
                                             let uu____5914 =
                                               let uu____5919 =
                                                 let uu____5920 =
                                                   FStar_TypeChecker_Env.inst_tscheme
                                                     ret_wp
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5920
                                                   FStar_Pervasives_Native.snd
                                                  in
                                               let uu____5929 =
                                                 let uu____5930 =
                                                   let uu____5939 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____5939
                                                     FStar_Syntax_Syntax.as_arg
                                                    in
                                                 let uu____5948 =
                                                   let uu____5959 =
                                                     let uu____5968 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         x_a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____5968
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   [uu____5959]  in
                                                 uu____5930 :: uu____5948  in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 uu____5919 uu____5929
                                                in
                                             uu____5914
                                               FStar_Pervasives_Native.None
                                               FStar_Range.dummyRange
                                              in
                                           mk_repr a wp  in
                                         let k =
                                           let uu____6004 =
                                             let uu____6013 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6020 =
                                               let uu____6029 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   x_a
                                                  in
                                               [uu____6029]  in
                                             uu____6013 :: uu____6020  in
                                           let uu____6054 =
                                             FStar_Syntax_Syntax.mk_Total res
                                              in
                                           FStar_Syntax_Util.arrow uu____6004
                                             uu____6054
                                            in
                                         let uu____6057 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env k
                                            in
                                         (match uu____6057 with
                                          | (k1,uu____6065,uu____6066) ->
                                              let env1 =
                                                let uu____6070 =
                                                  FStar_TypeChecker_Env.set_range
                                                    env
                                                    (FStar_Pervasives_Native.snd
                                                       ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6070
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
                                        let uu____6081 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            FStar_Parser_Const.range_0
                                            FStar_Syntax_Syntax.delta_constant
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_All.pipe_right uu____6081
                                          FStar_Syntax_Syntax.fv_to_tm
                                         in
                                      let uu____6082 = fresh_a_and_wp ()  in
                                      match uu____6082 with
                                      | (a,wp_sort_a) ->
                                          let uu____6095 = fresh_a_and_wp ()
                                             in
                                          (match uu____6095 with
                                           | (b,wp_sort_b) ->
                                               let wp_sort_a_b =
                                                 let uu____6111 =
                                                   let uu____6120 =
                                                     let uu____6127 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____6127
                                                      in
                                                   [uu____6120]  in
                                                 let uu____6140 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     wp_sort_b
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6111 uu____6140
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
                                                 let uu____6148 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     a
                                                    in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "x_a"
                                                   FStar_Pervasives_Native.None
                                                   uu____6148
                                                  in
                                               let wp_g_x =
                                                 let uu____6153 =
                                                   let uu____6158 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       wp_g
                                                      in
                                                   let uu____6159 =
                                                     let uu____6160 =
                                                       let uu____6169 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6169
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6160]  in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     uu____6158 uu____6159
                                                    in
                                                 uu____6153
                                                   FStar_Pervasives_Native.None
                                                   FStar_Range.dummyRange
                                                  in
                                               let res =
                                                 let wp =
                                                   let uu____6200 =
                                                     let uu____6205 =
                                                       let uu____6206 =
                                                         FStar_TypeChecker_Env.inst_tscheme
                                                           bind_wp
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6206
                                                         FStar_Pervasives_Native.snd
                                                        in
                                                     let uu____6215 =
                                                       let uu____6216 =
                                                         let uu____6219 =
                                                           let uu____6222 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               a
                                                              in
                                                           let uu____6223 =
                                                             let uu____6226 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 b
                                                                in
                                                             let uu____6227 =
                                                               let uu____6230
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               let uu____6231
                                                                 =
                                                                 let uu____6234
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g
                                                                    in
                                                                 [uu____6234]
                                                                  in
                                                               uu____6230 ::
                                                                 uu____6231
                                                                in
                                                             uu____6226 ::
                                                               uu____6227
                                                              in
                                                           uu____6222 ::
                                                             uu____6223
                                                            in
                                                         r :: uu____6219  in
                                                       FStar_List.map
                                                         FStar_Syntax_Syntax.as_arg
                                                         uu____6216
                                                        in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6205 uu____6215
                                                      in
                                                   uu____6200
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 mk_repr b wp  in
                                               let maybe_range_arg =
                                                 let uu____6252 =
                                                   FStar_Util.for_some
                                                     (FStar_Syntax_Util.attr_eq
                                                        FStar_Syntax_Util.dm4f_bind_range_attr)
                                                     ed2.FStar_Syntax_Syntax.eff_attrs
                                                    in
                                                 if uu____6252
                                                 then
                                                   let uu____6263 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       FStar_Syntax_Syntax.t_range
                                                      in
                                                   let uu____6270 =
                                                     let uu____6279 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     [uu____6279]  in
                                                   uu____6263 :: uu____6270
                                                 else []  in
                                               let k =
                                                 let uu____6315 =
                                                   let uu____6324 =
                                                     let uu____6333 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6340 =
                                                       let uu____6349 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           b
                                                          in
                                                       [uu____6349]  in
                                                     uu____6333 :: uu____6340
                                                      in
                                                   let uu____6374 =
                                                     let uu____6383 =
                                                       let uu____6392 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           wp_f
                                                          in
                                                       let uu____6399 =
                                                         let uu____6408 =
                                                           let uu____6415 =
                                                             let uu____6416 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp_f
                                                                in
                                                             mk_repr a
                                                               uu____6416
                                                              in
                                                           FStar_Syntax_Syntax.null_binder
                                                             uu____6415
                                                            in
                                                         let uu____6417 =
                                                           let uu____6426 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               wp_g
                                                              in
                                                           let uu____6433 =
                                                             let uu____6442 =
                                                               let uu____6449
                                                                 =
                                                                 let uu____6450
                                                                   =
                                                                   let uu____6459
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                   [uu____6459]
                                                                    in
                                                                 let uu____6478
                                                                   =
                                                                   let uu____6481
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                   FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6481
                                                                    in
                                                                 FStar_Syntax_Util.arrow
                                                                   uu____6450
                                                                   uu____6478
                                                                  in
                                                               FStar_Syntax_Syntax.null_binder
                                                                 uu____6449
                                                                in
                                                             [uu____6442]  in
                                                           uu____6426 ::
                                                             uu____6433
                                                            in
                                                         uu____6408 ::
                                                           uu____6417
                                                          in
                                                       uu____6392 ::
                                                         uu____6399
                                                        in
                                                     FStar_List.append
                                                       maybe_range_arg
                                                       uu____6383
                                                      in
                                                   FStar_List.append
                                                     uu____6324 uu____6374
                                                    in
                                                 let uu____6526 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     res
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   uu____6315 uu____6526
                                                  in
                                               let uu____6529 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env k
                                                  in
                                               (match uu____6529 with
                                                | (k1,uu____6537,uu____6538)
                                                    ->
                                                    let env1 =
                                                      FStar_TypeChecker_Env.set_range
                                                        env
                                                        (FStar_Pervasives_Native.snd
                                                           ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                       in
                                                    let env2 =
                                                      FStar_All.pipe_right
                                                        (let uu___693_6550 =
                                                           env1  in
                                                         {
                                                           FStar_TypeChecker_Env.solver
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.solver);
                                                           FStar_TypeChecker_Env.range
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.range);
                                                           FStar_TypeChecker_Env.curmodule
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.curmodule);
                                                           FStar_TypeChecker_Env.gamma
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.gamma);
                                                           FStar_TypeChecker_Env.gamma_sig
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.gamma_sig);
                                                           FStar_TypeChecker_Env.gamma_cache
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.gamma_cache);
                                                           FStar_TypeChecker_Env.modules
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.modules);
                                                           FStar_TypeChecker_Env.expected_typ
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.expected_typ);
                                                           FStar_TypeChecker_Env.sigtab
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.sigtab);
                                                           FStar_TypeChecker_Env.attrtab
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.attrtab);
                                                           FStar_TypeChecker_Env.is_pattern
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.is_pattern);
                                                           FStar_TypeChecker_Env.instantiate_imp
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.instantiate_imp);
                                                           FStar_TypeChecker_Env.effects
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.effects);
                                                           FStar_TypeChecker_Env.generalize
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.generalize);
                                                           FStar_TypeChecker_Env.letrecs
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.letrecs);
                                                           FStar_TypeChecker_Env.top_level
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.top_level);
                                                           FStar_TypeChecker_Env.check_uvars
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.check_uvars);
                                                           FStar_TypeChecker_Env.use_eq
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.use_eq);
                                                           FStar_TypeChecker_Env.is_iface
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.is_iface);
                                                           FStar_TypeChecker_Env.admit
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.admit);
                                                           FStar_TypeChecker_Env.lax
                                                             = true;
                                                           FStar_TypeChecker_Env.lax_universes
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.lax_universes);
                                                           FStar_TypeChecker_Env.phase1
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.phase1);
                                                           FStar_TypeChecker_Env.failhard
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.failhard);
                                                           FStar_TypeChecker_Env.nosynth
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.nosynth);
                                                           FStar_TypeChecker_Env.uvar_subtyping
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.uvar_subtyping);
                                                           FStar_TypeChecker_Env.tc_term
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.tc_term);
                                                           FStar_TypeChecker_Env.type_of
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.type_of);
                                                           FStar_TypeChecker_Env.universe_of
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.universe_of);
                                                           FStar_TypeChecker_Env.check_type_of
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.check_type_of);
                                                           FStar_TypeChecker_Env.use_bv_sorts
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.use_bv_sorts);
                                                           FStar_TypeChecker_Env.qtbl_name_and_index
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                           FStar_TypeChecker_Env.normalized_eff_names
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.normalized_eff_names);
                                                           FStar_TypeChecker_Env.fv_delta_depths
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.fv_delta_depths);
                                                           FStar_TypeChecker_Env.proof_ns
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.proof_ns);
                                                           FStar_TypeChecker_Env.synth_hook
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.synth_hook);
                                                           FStar_TypeChecker_Env.try_solve_implicits_hook
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                           FStar_TypeChecker_Env.splice
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.splice);
                                                           FStar_TypeChecker_Env.postprocess
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.postprocess);
                                                           FStar_TypeChecker_Env.is_native_tactic
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.is_native_tactic);
                                                           FStar_TypeChecker_Env.identifier_info
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.identifier_info);
                                                           FStar_TypeChecker_Env.tc_hooks
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.tc_hooks);
                                                           FStar_TypeChecker_Env.dsenv
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.dsenv);
                                                           FStar_TypeChecker_Env.nbe
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.nbe);
                                                           FStar_TypeChecker_Env.strict_args_tab
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.strict_args_tab);
                                                           FStar_TypeChecker_Env.erasable_types_tab
                                                             =
                                                             (uu___693_6550.FStar_TypeChecker_Env.erasable_types_tab)
                                                         })
                                                        (fun _6552  ->
                                                           FStar_Pervasives_Native.Some
                                                             _6552)
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
                                         (let uu____6579 =
                                            if
                                              act.FStar_Syntax_Syntax.action_univs
                                                = []
                                            then (env, act)
                                            else
                                              (let uu____6593 =
                                                 FStar_Syntax_Subst.univ_var_opening
                                                   act.FStar_Syntax_Syntax.action_univs
                                                  in
                                               match uu____6593 with
                                               | (usubst,uvs) ->
                                                   let uu____6616 =
                                                     FStar_TypeChecker_Env.push_univ_vars
                                                       env uvs
                                                      in
                                                   let uu____6617 =
                                                     let uu___706_6618 = act
                                                        in
                                                     let uu____6619 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     let uu____6620 =
                                                       FStar_Syntax_Subst.subst
                                                         usubst
                                                         act.FStar_Syntax_Syntax.action_typ
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___706_6618.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___706_6618.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         = uvs;
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___706_6618.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____6619;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____6620
                                                     }  in
                                                   (uu____6616, uu____6617))
                                             in
                                          match uu____6579 with
                                          | (env1,act1) ->
                                              let act_typ =
                                                let uu____6624 =
                                                  let uu____6625 =
                                                    FStar_Syntax_Subst.compress
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                     in
                                                  uu____6625.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____6624 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs1,c) ->
                                                    let c1 =
                                                      FStar_Syntax_Util.comp_to_comp_typ
                                                        c
                                                       in
                                                    let uu____6651 =
                                                      FStar_Ident.lid_equals
                                                        c1.FStar_Syntax_Syntax.effect_name
                                                        ed2.FStar_Syntax_Syntax.mname
                                                       in
                                                    if uu____6651
                                                    then
                                                      let uu____6654 =
                                                        let uu____6657 =
                                                          let uu____6658 =
                                                            let uu____6659 =
                                                              FStar_List.hd
                                                                c1.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____6659
                                                             in
                                                          mk_repr'
                                                            c1.FStar_Syntax_Syntax.result_typ
                                                            uu____6658
                                                           in
                                                        FStar_Syntax_Syntax.mk_Total
                                                          uu____6657
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        bs1 uu____6654
                                                    else
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                | uu____6682 ->
                                                    act1.FStar_Syntax_Syntax.action_typ
                                                 in
                                              let uu____6683 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env1 act_typ
                                                 in
                                              (match uu____6683 with
                                               | (act_typ1,uu____6691,g_t) ->
                                                   let env' =
                                                     let uu___723_6694 =
                                                       FStar_TypeChecker_Env.set_expected_typ
                                                         env1 act_typ1
                                                        in
                                                     {
                                                       FStar_TypeChecker_Env.solver
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.solver);
                                                       FStar_TypeChecker_Env.range
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.range);
                                                       FStar_TypeChecker_Env.curmodule
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.curmodule);
                                                       FStar_TypeChecker_Env.gamma
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.gamma);
                                                       FStar_TypeChecker_Env.gamma_sig
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.gamma_sig);
                                                       FStar_TypeChecker_Env.gamma_cache
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.gamma_cache);
                                                       FStar_TypeChecker_Env.modules
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.modules);
                                                       FStar_TypeChecker_Env.expected_typ
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.expected_typ);
                                                       FStar_TypeChecker_Env.sigtab
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.sigtab);
                                                       FStar_TypeChecker_Env.attrtab
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.attrtab);
                                                       FStar_TypeChecker_Env.is_pattern
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.is_pattern);
                                                       FStar_TypeChecker_Env.instantiate_imp
                                                         = false;
                                                       FStar_TypeChecker_Env.effects
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.effects);
                                                       FStar_TypeChecker_Env.generalize
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.generalize);
                                                       FStar_TypeChecker_Env.letrecs
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.letrecs);
                                                       FStar_TypeChecker_Env.top_level
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.top_level);
                                                       FStar_TypeChecker_Env.check_uvars
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.check_uvars);
                                                       FStar_TypeChecker_Env.use_eq
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.use_eq);
                                                       FStar_TypeChecker_Env.is_iface
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.is_iface);
                                                       FStar_TypeChecker_Env.admit
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.admit);
                                                       FStar_TypeChecker_Env.lax
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.lax);
                                                       FStar_TypeChecker_Env.lax_universes
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.lax_universes);
                                                       FStar_TypeChecker_Env.phase1
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.phase1);
                                                       FStar_TypeChecker_Env.failhard
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.failhard);
                                                       FStar_TypeChecker_Env.nosynth
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.nosynth);
                                                       FStar_TypeChecker_Env.uvar_subtyping
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.uvar_subtyping);
                                                       FStar_TypeChecker_Env.tc_term
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.tc_term);
                                                       FStar_TypeChecker_Env.type_of
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.type_of);
                                                       FStar_TypeChecker_Env.universe_of
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.universe_of);
                                                       FStar_TypeChecker_Env.check_type_of
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.check_type_of);
                                                       FStar_TypeChecker_Env.use_bv_sorts
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.use_bv_sorts);
                                                       FStar_TypeChecker_Env.qtbl_name_and_index
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                       FStar_TypeChecker_Env.normalized_eff_names
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.normalized_eff_names);
                                                       FStar_TypeChecker_Env.fv_delta_depths
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.fv_delta_depths);
                                                       FStar_TypeChecker_Env.proof_ns
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.proof_ns);
                                                       FStar_TypeChecker_Env.synth_hook
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.synth_hook);
                                                       FStar_TypeChecker_Env.try_solve_implicits_hook
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                       FStar_TypeChecker_Env.splice
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.splice);
                                                       FStar_TypeChecker_Env.postprocess
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.postprocess);
                                                       FStar_TypeChecker_Env.is_native_tactic
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.is_native_tactic);
                                                       FStar_TypeChecker_Env.identifier_info
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.identifier_info);
                                                       FStar_TypeChecker_Env.tc_hooks
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.tc_hooks);
                                                       FStar_TypeChecker_Env.dsenv
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.dsenv);
                                                       FStar_TypeChecker_Env.nbe
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.nbe);
                                                       FStar_TypeChecker_Env.strict_args_tab
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.strict_args_tab);
                                                       FStar_TypeChecker_Env.erasable_types_tab
                                                         =
                                                         (uu___723_6694.FStar_TypeChecker_Env.erasable_types_tab)
                                                     }  in
                                                   ((let uu____6697 =
                                                       FStar_TypeChecker_Env.debug
                                                         env1
                                                         (FStar_Options.Other
                                                            "ED")
                                                        in
                                                     if uu____6697
                                                     then
                                                       let uu____6701 =
                                                         FStar_Ident.text_of_lid
                                                           act1.FStar_Syntax_Syntax.action_name
                                                          in
                                                       let uu____6703 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6705 =
                                                         FStar_Syntax_Print.term_to_string
                                                           act_typ1
                                                          in
                                                       FStar_Util.print3
                                                         "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                         uu____6701
                                                         uu____6703
                                                         uu____6705
                                                     else ());
                                                    (let uu____6710 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env'
                                                         act1.FStar_Syntax_Syntax.action_defn
                                                        in
                                                     match uu____6710 with
                                                     | (act_defn,uu____6718,g_a)
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
                                                         let uu____6722 =
                                                           let act_typ3 =
                                                             FStar_Syntax_Subst.compress
                                                               act_typ2
                                                              in
                                                           match act_typ3.FStar_Syntax_Syntax.n
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1,c) ->
                                                               let uu____6758
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c
                                                                  in
                                                               (match uu____6758
                                                                with
                                                                | (bs2,uu____6770)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6777
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6777
                                                                     in
                                                                    let uu____6780
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6780
                                                                    with
                                                                    | 
                                                                    (k1,uu____6794,g)
                                                                    ->
                                                                    (k1, g)))
                                                           | uu____6798 ->
                                                               let uu____6799
                                                                 =
                                                                 let uu____6805
                                                                   =
                                                                   let uu____6807
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                   let uu____6809
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                   FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____6807
                                                                    uu____6809
                                                                    in
                                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                   uu____6805)
                                                                  in
                                                               FStar_Errors.raise_error
                                                                 uu____6799
                                                                 act_defn1.FStar_Syntax_Syntax.pos
                                                            in
                                                         (match uu____6722
                                                          with
                                                          | (expected_k,g_k)
                                                              ->
                                                              let g =
                                                                FStar_TypeChecker_Rel.teq
                                                                  env1
                                                                  act_typ2
                                                                  expected_k
                                                                 in
                                                              ((let uu____6827
                                                                  =
                                                                  let uu____6828
                                                                    =
                                                                    let uu____6829
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____6829
                                                                     in
                                                                  FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____6828
                                                                   in
                                                                FStar_TypeChecker_Rel.force_trivial_guard
                                                                  env1
                                                                  uu____6827);
                                                               (let act_typ3
                                                                  =
                                                                  let uu____6831
                                                                    =
                                                                    let uu____6832
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____6832.FStar_Syntax_Syntax.n
                                                                     in
                                                                  match uu____6831
                                                                  with
                                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____6857
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____6857
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____6864
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____6864
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____6884
                                                                    =
                                                                    let uu____6885
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____6885]
                                                                     in
                                                                    let uu____6886
                                                                    =
                                                                    let uu____6897
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____6897]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____6884;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____6886;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____6922
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6922))
                                                                  | uu____6925
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                   in
                                                                let uu____6927
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
                                                                    let uu____6949
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____6949))
                                                                   in
                                                                match uu____6927
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
                                                                    let uu___773_6968
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___773_6968.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___773_6968.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___773_6968.FStar_Syntax_Syntax.action_params);
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
                           match uu____5525 with
                           | (repr,return_repr,bind_repr,actions) ->
                               let cl ts =
                                 let ts1 =
                                   FStar_Syntax_Subst.close_tscheme ed_bs ts
                                    in
                                 let ed_univs_closing =
                                   FStar_Syntax_Subst.univ_var_closing
                                     ed_univs
                                    in
                                 let uu____6993 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length ed_bs)
                                     ed_univs_closing
                                    in
                                 FStar_Syntax_Subst.subst_tscheme uu____6993
                                   ts1
                                  in
                               let ed3 =
                                 let uu___785_7003 = ed2  in
                                 let uu____7004 = cl signature  in
                                 let uu____7005 = cl ret_wp  in
                                 let uu____7006 = cl bind_wp  in
                                 let uu____7007 = cl stronger  in
                                 let uu____7008 =
                                   FStar_Syntax_Util.map_match_wps cl
                                     match_wps
                                    in
                                 let uu____7013 =
                                   FStar_Util.map_opt trivial cl  in
                                 let uu____7016 = cl repr  in
                                 let uu____7017 = cl return_repr  in
                                 let uu____7018 = cl bind_repr  in
                                 let uu____7019 =
                                   FStar_List.map
                                     (fun a  ->
                                        let uu___788_7027 = a  in
                                        let uu____7028 =
                                          let uu____7029 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_All.pipe_right uu____7029
                                            FStar_Pervasives_Native.snd
                                           in
                                        let uu____7054 =
                                          let uu____7055 =
                                            cl
                                              ((a.FStar_Syntax_Syntax.action_univs),
                                                (a.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_All.pipe_right uu____7055
                                            FStar_Pervasives_Native.snd
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            (uu___788_7027.FStar_Syntax_Syntax.action_name);
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (uu___788_7027.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (uu___788_7027.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (uu___788_7027.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____7028;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____7054
                                        }) actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.is_layered =
                                     (uu___785_7003.FStar_Syntax_Syntax.is_layered);
                                   FStar_Syntax_Syntax.cattributes =
                                     (uu___785_7003.FStar_Syntax_Syntax.cattributes);
                                   FStar_Syntax_Syntax.mname =
                                     (uu___785_7003.FStar_Syntax_Syntax.mname);
                                   FStar_Syntax_Syntax.univs =
                                     (uu___785_7003.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders =
                                     (uu___785_7003.FStar_Syntax_Syntax.binders);
                                   FStar_Syntax_Syntax.signature = uu____7004;
                                   FStar_Syntax_Syntax.ret_wp = uu____7005;
                                   FStar_Syntax_Syntax.bind_wp = uu____7006;
                                   FStar_Syntax_Syntax.stronger = uu____7007;
                                   FStar_Syntax_Syntax.match_wps = uu____7008;
                                   FStar_Syntax_Syntax.trivial = uu____7013;
                                   FStar_Syntax_Syntax.repr = uu____7016;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____7017;
                                   FStar_Syntax_Syntax.bind_repr = uu____7018;
                                   FStar_Syntax_Syntax.stronger_repr =
                                     FStar_Pervasives_Native.None;
                                   FStar_Syntax_Syntax.actions = uu____7019;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (uu___785_7003.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               ((let uu____7081 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____7081
                                 then
                                   let uu____7086 =
                                     FStar_Syntax_Print.eff_decl_to_string
                                       false ed3
                                      in
                                   FStar_Util.print1
                                     "Typechecked effect declaration:\n\t%s\n"
                                     uu____7086
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
        let fail1 uu____7139 =
          let uu____7140 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____7146 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____7140 uu____7146  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____7190)::(wp,uu____7192)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____7221 -> fail1 ())
        | uu____7222 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____7235 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____7235
       then
         let uu____7240 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____7240
       else ());
      (let uu____7245 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____7245 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           let uu____7291 =
             if (FStar_List.length us) = Prims.int_zero
             then (env0, us, lift)
             else
               (let uu____7315 = FStar_Syntax_Subst.open_univ_vars us lift
                   in
                match uu____7315 with
                | (us1,lift1) ->
                    let uu____7330 =
                      FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                    (uu____7330, us1, lift1))
              in
           (match uu____7291 with
            | (env,us1,lift1) ->
                let uu____7340 =
                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                (match uu____7340 with
                 | (lift2,lc,g) ->
                     (FStar_TypeChecker_Rel.force_trivial_guard env g;
                      (let lift_ty =
                         FStar_All.pipe_right
                           lc.FStar_TypeChecker_Common.res_typ
                           (FStar_TypeChecker_Normalize.normalize
                              [FStar_TypeChecker_Env.Beta] env0)
                          in
                       (let uu____7353 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env0)
                            (FStar_Options.Other "LayeredEffects")
                           in
                        if uu____7353
                        then
                          let uu____7358 =
                            FStar_Syntax_Print.term_to_string lift2  in
                          let uu____7360 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.print2
                            "Typechecked lift: %s and lift_ty: %s\n"
                            uu____7358 uu____7360
                        else ());
                       (let lift_t_shape_error s =
                          let uu____7374 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.source
                             in
                          let uu____7376 =
                            FStar_Ident.string_of_lid
                              sub1.FStar_Syntax_Syntax.target
                             in
                          let uu____7378 =
                            FStar_Syntax_Print.term_to_string lift_ty  in
                          FStar_Util.format4
                            "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                            uu____7374 uu____7376 s uu____7378
                           in
                        let uu____7381 =
                          let uu____7388 =
                            let uu____7393 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_right uu____7393
                              (fun uu____7410  ->
                                 match uu____7410 with
                                 | (t,u) ->
                                     let uu____7421 =
                                       let uu____7422 =
                                         FStar_Syntax_Syntax.gen_bv "a"
                                           FStar_Pervasives_Native.None t
                                          in
                                       FStar_All.pipe_right uu____7422
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____7421, u))
                             in
                          match uu____7388 with
                          | (a,u_a) ->
                              let rest_bs =
                                let uu____7441 =
                                  let uu____7442 =
                                    FStar_Syntax_Subst.compress lift_ty  in
                                  uu____7442.FStar_Syntax_Syntax.n  in
                                match uu____7441 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs,uu____7454) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____7482 =
                                      FStar_Syntax_Subst.open_binders bs  in
                                    (match uu____7482 with
                                     | (a',uu____7492)::bs1 ->
                                         let uu____7512 =
                                           let uu____7513 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     Prims.int_one))
                                              in
                                           FStar_All.pipe_right uu____7513
                                             FStar_Pervasives_Native.fst
                                            in
                                         let uu____7611 =
                                           let uu____7624 =
                                             let uu____7627 =
                                               let uu____7628 =
                                                 let uu____7635 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a)
                                                    in
                                                 (a', uu____7635)  in
                                               FStar_Syntax_Syntax.NT
                                                 uu____7628
                                                in
                                             [uu____7627]  in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____7624
                                            in
                                         FStar_All.pipe_right uu____7512
                                           uu____7611)
                                | uu____7650 ->
                                    let uu____7651 =
                                      let uu____7657 =
                                        lift_t_shape_error
                                          "either not an arrow, or not enough binders"
                                         in
                                      (FStar_Errors.Fatal_UnexpectedExpressionType,
                                        uu____7657)
                                       in
                                    FStar_Errors.raise_error uu____7651 r
                                 in
                              let uu____7669 =
                                let uu____7680 =
                                  let uu____7685 =
                                    FStar_TypeChecker_Env.push_binders env (a
                                      :: rest_bs)
                                     in
                                  let uu____7692 =
                                    let uu____7693 =
                                      FStar_All.pipe_right a
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_All.pipe_right uu____7693
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  FStar_TypeChecker_Util.fresh_effect_repr_en
                                    uu____7685 r
                                    sub1.FStar_Syntax_Syntax.source u_a
                                    uu____7692
                                   in
                                match uu____7680 with
                                | (f_sort,g1) ->
                                    let uu____7714 =
                                      let uu____7721 =
                                        FStar_Syntax_Syntax.gen_bv "f"
                                          FStar_Pervasives_Native.None f_sort
                                         in
                                      FStar_All.pipe_right uu____7721
                                        FStar_Syntax_Syntax.mk_binder
                                       in
                                    (uu____7714, g1)
                                 in
                              (match uu____7669 with
                               | (f_b,g_f_b) ->
                                   let bs = a ::
                                     (FStar_List.append rest_bs [f_b])  in
                                   let uu____7788 =
                                     let uu____7793 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____7794 =
                                       let uu____7795 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____7795
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_effect_repr_en
                                       uu____7793 r
                                       sub1.FStar_Syntax_Syntax.target u_a
                                       uu____7794
                                      in
                                   (match uu____7788 with
                                    | (repr,g_repr) ->
                                        let uu____7812 =
                                          let uu____7815 =
                                            let uu____7818 =
                                              let uu____7821 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              FStar_All.pipe_right uu____7821
                                                (fun _7824  ->
                                                   FStar_Pervasives_Native.Some
                                                     _7824)
                                               in
                                            FStar_Syntax_Syntax.mk_Total'
                                              repr uu____7818
                                             in
                                          FStar_Syntax_Util.arrow bs
                                            uu____7815
                                           in
                                        let uu____7825 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_f_b g_repr
                                           in
                                        (uu____7812, uu____7825)))
                           in
                        match uu____7381 with
                        | (k,g_k) ->
                            ((let uu____7835 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "LayeredEffects")
                                 in
                              if uu____7835
                              then
                                let uu____7840 =
                                  FStar_Syntax_Print.term_to_string k  in
                                FStar_Util.print1
                                  "tc_layered_lift: before unification k: %s\n"
                                  uu____7840
                              else ());
                             (let g1 =
                                FStar_TypeChecker_Rel.teq env lift_ty k  in
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g_k;
                              FStar_TypeChecker_Rel.force_trivial_guard env
                                g1;
                              (let uu____7849 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env0)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____7849
                               then
                                 let uu____7854 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "After unification k: %s\n" uu____7854
                               else ());
                              (let uu____7859 =
                                 let uu____7872 =
                                   FStar_TypeChecker_Util.generalize_universes
                                     env0 lift2
                                    in
                                 match uu____7872 with
                                 | (inst_us,lift3) ->
                                     (if
                                        (FStar_List.length inst_us) <>
                                          Prims.int_one
                                      then
                                        (let uu____7899 =
                                           let uu____7905 =
                                             let uu____7907 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.source
                                                in
                                             let uu____7909 =
                                               FStar_Ident.string_of_lid
                                                 sub1.FStar_Syntax_Syntax.target
                                                in
                                             let uu____7911 =
                                               let uu____7913 =
                                                 FStar_All.pipe_right inst_us
                                                   FStar_List.length
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7913
                                                 FStar_Util.string_of_int
                                                in
                                             let uu____7920 =
                                               FStar_Syntax_Print.term_to_string
                                                 lift3
                                                in
                                             FStar_Util.format4
                                               "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                               uu____7907 uu____7909
                                               uu____7911 uu____7920
                                              in
                                           (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                             uu____7905)
                                            in
                                         FStar_Errors.raise_error uu____7899
                                           r)
                                      else ();
                                      (let uu____7926 =
                                         ((FStar_List.length us1) =
                                            Prims.int_zero)
                                           ||
                                           (((FStar_List.length us1) =
                                               (FStar_List.length inst_us))
                                              &&
                                              (FStar_List.forall2
                                                 (fun u1  ->
                                                    fun u2  ->
                                                      let uu____7935 =
                                                        FStar_Syntax_Syntax.order_univ_name
                                                          u1 u2
                                                         in
                                                      uu____7935 =
                                                        Prims.int_zero) us1
                                                 inst_us))
                                          in
                                       if uu____7926
                                       then
                                         let uu____7952 =
                                           let uu____7955 =
                                             FStar_All.pipe_right k
                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                  env)
                                              in
                                           FStar_All.pipe_right uu____7955
                                             (FStar_Syntax_Subst.close_univ_vars
                                                inst_us)
                                            in
                                         (inst_us, lift3, uu____7952)
                                       else
                                         (let uu____7966 =
                                            let uu____7972 =
                                              let uu____7974 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____7976 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____7978 =
                                                let uu____7980 =
                                                  FStar_All.pipe_right us1
                                                    FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7980
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7987 =
                                                let uu____7989 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____7989
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____7996 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format5
                                                "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                uu____7974 uu____7976
                                                uu____7978 uu____7987
                                                uu____7996
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____7972)
                                             in
                                          FStar_Errors.raise_error uu____7966
                                            r)))
                                  in
                               match uu____7859 with
                               | (us2,lift3,lift_wp) ->
                                   let sub2 =
                                     let uu___891_8028 = sub1  in
                                     {
                                       FStar_Syntax_Syntax.source =
                                         (uu___891_8028.FStar_Syntax_Syntax.source);
                                       FStar_Syntax_Syntax.target =
                                         (uu___891_8028.FStar_Syntax_Syntax.target);
                                       FStar_Syntax_Syntax.lift_wp =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift_wp));
                                       FStar_Syntax_Syntax.lift =
                                         (FStar_Pervasives_Native.Some
                                            (us2, lift3))
                                     }  in
                                   ((let uu____8038 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env0)
                                         (FStar_Options.Other
                                            "LayeredEffects")
                                        in
                                     if uu____8038
                                     then
                                       let uu____8043 =
                                         FStar_Syntax_Print.sub_eff_to_string
                                           sub2
                                          in
                                       FStar_Util.print1
                                         "Final sub_effect: %s\n" uu____8043
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
          (let uu____8069 =
             let uu____8076 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8076
              in
           match uu____8069 with
           | (a,wp_a_src) ->
               let uu____8083 =
                 let uu____8090 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____8090
                  in
               (match uu____8083 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____8098 =
                        let uu____8101 =
                          let uu____8102 =
                            let uu____8109 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____8109)  in
                          FStar_Syntax_Syntax.NT uu____8102  in
                        [uu____8101]  in
                      FStar_Syntax_Subst.subst uu____8098 wp_b_tgt  in
                    let expected_k =
                      let uu____8117 =
                        let uu____8126 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____8133 =
                          let uu____8142 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____8142]  in
                        uu____8126 :: uu____8133  in
                      let uu____8167 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____8117 uu____8167  in
                    let repr_type eff_name a1 wp =
                      (let uu____8189 =
                         let uu____8191 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____8191  in
                       if uu____8189
                       then
                         let uu____8194 =
                           let uu____8200 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____8200)
                            in
                         let uu____8204 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____8194 uu____8204
                       else ());
                      (let uu____8207 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____8207 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____8240 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____8241 =
                             let uu____8248 =
                               let uu____8249 =
                                 let uu____8266 =
                                   let uu____8277 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____8286 =
                                     let uu____8297 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____8297]  in
                                   uu____8277 :: uu____8286  in
                                 (repr, uu____8266)  in
                               FStar_Syntax_Syntax.Tm_app uu____8249  in
                             FStar_Syntax_Syntax.mk uu____8248  in
                           uu____8241 FStar_Pervasives_Native.None uu____8240)
                       in
                    let uu____8342 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____8515 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____8526 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____8526 with
                              | (usubst,uvs1) ->
                                  let uu____8549 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8550 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8549, uu____8550)
                            else (env, lift_wp)  in
                          (match uu____8515 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8600 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8600))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8671 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8686 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8686 with
                              | (usubst,uvs) ->
                                  let uu____8711 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8711)
                            else ([], lift)  in
                          (match uu____8671 with
                           | (uvs,lift1) ->
                               ((let uu____8747 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____8747
                                 then
                                   let uu____8751 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____8751
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____8757 =
                                   let uu____8764 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____8764 lift1
                                    in
                                 match uu____8757 with
                                 | (lift2,comp,uu____8789) ->
                                     let uu____8790 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____8790 with
                                      | (uu____8819,lift_wp,lift_elab) ->
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
                                            let uu____8851 =
                                              let uu____8862 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____8862
                                               in
                                            let uu____8879 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____8851, uu____8879)
                                          else
                                            (let uu____8908 =
                                               let uu____8919 =
                                                 let uu____8928 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____8928)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____8919
                                                in
                                             let uu____8943 =
                                               let uu____8952 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____8952)  in
                                             (uu____8908, uu____8943))))))
                       in
                    (match uu____8342 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___971_9016 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___971_9016.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___971_9016.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___971_9016.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___971_9016.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___971_9016.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___971_9016.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___971_9016.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___971_9016.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___971_9016.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___971_9016.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.is_pattern =
                               (uu___971_9016.FStar_TypeChecker_Env.is_pattern);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___971_9016.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___971_9016.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___971_9016.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___971_9016.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___971_9016.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___971_9016.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___971_9016.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___971_9016.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___971_9016.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___971_9016.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___971_9016.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___971_9016.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___971_9016.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___971_9016.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___971_9016.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___971_9016.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___971_9016.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___971_9016.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___971_9016.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___971_9016.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___971_9016.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___971_9016.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___971_9016.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___971_9016.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___971_9016.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___971_9016.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___971_9016.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___971_9016.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___971_9016.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___971_9016.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___971_9016.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___971_9016.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___971_9016.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___971_9016.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____9049 =
                                 let uu____9054 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9054 with
                                 | (usubst,uvs1) ->
                                     let uu____9077 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____9078 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____9077, uu____9078)
                                  in
                               (match uu____9049 with
                                | (env2,lift2) ->
                                    let uu____9083 =
                                      let uu____9090 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____9090
                                       in
                                    (match uu____9083 with
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
                                             let uu____9116 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____9117 =
                                               let uu____9124 =
                                                 let uu____9125 =
                                                   let uu____9142 =
                                                     let uu____9153 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____9162 =
                                                       let uu____9173 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____9173]  in
                                                     uu____9153 :: uu____9162
                                                      in
                                                   (lift_wp1, uu____9142)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____9125
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9124
                                                in
                                             uu____9117
                                               FStar_Pervasives_Native.None
                                               uu____9116
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____9221 =
                                             let uu____9230 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____9237 =
                                               let uu____9246 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____9253 =
                                                 let uu____9262 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____9262]  in
                                               uu____9246 :: uu____9253  in
                                             uu____9230 :: uu____9237  in
                                           let uu____9293 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____9221
                                             uu____9293
                                            in
                                         let uu____9296 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____9296 with
                                          | (expected_k2,uu____9306,uu____9307)
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
                                                   let uu____9315 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____9315))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____9323 =
                             let uu____9325 =
                               let uu____9327 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____9327
                                 FStar_List.length
                                in
                             uu____9325 <> Prims.int_one  in
                           if uu____9323
                           then
                             let uu____9350 =
                               let uu____9356 =
                                 let uu____9358 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9360 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9362 =
                                   let uu____9364 =
                                     let uu____9366 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9366
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9364
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9358 uu____9360 uu____9362
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9356)
                                in
                             FStar_Errors.raise_error uu____9350 r
                           else ());
                          (let uu____9393 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____9396 =
                                  let uu____9398 =
                                    let uu____9401 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____9401
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____9398
                                    FStar_List.length
                                   in
                                uu____9396 <> Prims.int_one)
                              in
                           if uu____9393
                           then
                             let uu____9439 =
                               let uu____9445 =
                                 let uu____9447 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9449 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9451 =
                                   let uu____9453 =
                                     let uu____9455 =
                                       let uu____9458 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____9458
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9455
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9453
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9447 uu____9449 uu____9451
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9445)
                                in
                             FStar_Errors.raise_error uu____9439 r
                           else ());
                          (let uu___1008_9500 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1008_9500.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1008_9500.FStar_Syntax_Syntax.target);
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
    fun uu____9531  ->
      fun r  ->
        match uu____9531 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9554 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9582 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9582 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9613 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9613 c  in
                     let uu____9622 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9622, uvs1, tps1, c1))
               in
            (match uu____9554 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9642 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9642 with
                  | (tps2,c2) ->
                      let uu____9657 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9657 with
                       | (tps3,env3,us) ->
                           let uu____9675 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____9675 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____9701)::uu____9702 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____9721 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____9729 =
                                    let uu____9731 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____9731  in
                                  if uu____9729
                                  then
                                    let uu____9734 =
                                      let uu____9740 =
                                        let uu____9742 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____9744 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____9742 uu____9744
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____9740)
                                       in
                                    FStar_Errors.raise_error uu____9734 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____9752 =
                                    let uu____9753 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____9753
                                     in
                                  match uu____9752 with
                                  | (uvs2,t) ->
                                      let uu____9782 =
                                        let uu____9787 =
                                          let uu____9800 =
                                            let uu____9801 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____9801.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____9800)  in
                                        match uu____9787 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____9816,c5)) -> ([], c5)
                                        | (uu____9858,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____9897 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____9782 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____9929 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____9929 with
                                               | (uu____9934,t1) ->
                                                   let uu____9936 =
                                                     let uu____9942 =
                                                       let uu____9944 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____9946 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____9950 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____9944
                                                         uu____9946
                                                         uu____9950
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____9942)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____9936 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  