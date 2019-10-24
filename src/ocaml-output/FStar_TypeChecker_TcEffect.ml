open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____41 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____41
         then
           let uu____46 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n" uu____46
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____64 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____64)
        else ();
        (let check_and_gen comb n1 uu____97 =
           match uu____97 with
           | (us,t) ->
               let uu____118 = FStar_Syntax_Subst.open_univ_vars us t  in
               (match uu____118 with
                | (us1,t1) ->
                    let uu____131 =
                      let uu____136 =
                        let uu____143 =
                          FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                          uu____143 t1
                         in
                      match uu____136 with
                      | (t2,lc,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env0 g;
                           (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                       in
                    (match uu____131 with
                     | (t2,ty) ->
                         let uu____160 =
                           FStar_TypeChecker_Util.generalize_universes env0
                             t2
                            in
                         (match uu____160 with
                          | (g_us,t3) ->
                              let ty1 =
                                FStar_Syntax_Subst.close_univ_vars g_us ty
                                 in
                              (if (FStar_List.length g_us) <> n1
                               then
                                 (let error =
                                    let uu____183 =
                                      FStar_Util.string_of_int n1  in
                                    let uu____185 =
                                      let uu____187 =
                                        FStar_All.pipe_right g_us
                                          FStar_List.length
                                         in
                                      FStar_All.pipe_right uu____187
                                        FStar_Util.string_of_int
                                       in
                                    let uu____194 =
                                      FStar_Syntax_Print.tscheme_to_string
                                        (g_us, t3)
                                       in
                                    FStar_Util.format5
                                      "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                      comb uu____183 uu____185 uu____194
                                     in
                                  FStar_Errors.raise_error
                                    (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                      error) t3.FStar_Syntax_Syntax.pos;
                                  (match us1 with
                                   | [] -> ()
                                   | uu____203 ->
                                       let uu____204 =
                                         ((FStar_List.length us1) =
                                            (FStar_List.length g_us))
                                           &&
                                           (FStar_List.forall2
                                              (fun u1  ->
                                                 fun u2  ->
                                                   let uu____211 =
                                                     FStar_Syntax_Syntax.order_univ_name
                                                       u1 u2
                                                      in
                                                   uu____211 = Prims.int_zero)
                                              us1 g_us)
                                          in
                                       if uu____204
                                       then ()
                                       else
                                         (let uu____218 =
                                            let uu____224 =
                                              let uu____226 =
                                                FStar_Syntax_Print.univ_names_to_string
                                                  us1
                                                 in
                                              let uu____228 =
                                                FStar_Syntax_Print.univ_names_to_string
                                                  g_us
                                                 in
                                              FStar_Util.format4
                                                "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                comb uu____226 uu____228
                                               in
                                            (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                              uu____224)
                                             in
                                          FStar_Errors.raise_error uu____218
                                            t3.FStar_Syntax_Syntax.pos)))
                               else ();
                               (g_us, t3, ty1)))))
            in
         let log_combinator s uu____257 =
           match uu____257 with
           | (us,t,ty) ->
               let uu____286 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____286
               then
                 let uu____291 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____297 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____291
                   uu____297
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____322 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____322
             (fun uu____339  ->
                match uu____339 with
                | (t,u) ->
                    let uu____350 =
                      let uu____351 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____351
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____350, u))
            in
         let fresh_x_a x a =
           let uu____365 =
             let uu____366 =
               let uu____367 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____367 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____366
              in
           FStar_All.pipe_right uu____365 FStar_Syntax_Syntax.mk_binder  in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____394 =
             check_and_gen "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____394 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____418 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____418 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____438 = fresh_a_and_u_a "a"  in
                    (match uu____438 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____459 =
                             let uu____460 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____460
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____459
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____491 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____491  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____496 =
                             let uu____499 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____499
                              in
                           (sig_us, uu____496, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____508 =
            let r =
              (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.pos
               in
            let uu____530 =
              check_and_gen "repr" Prims.int_one ed.FStar_Syntax_Syntax.repr
               in
            match uu____530 with
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
                  let uu____561 =
                    let uu____562 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____562.FStar_Syntax_Syntax.n  in
                  match uu____561 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____565,t,uu____567) ->
                      let uu____592 =
                        let uu____593 = FStar_Syntax_Subst.compress t  in
                        uu____593.FStar_Syntax_Syntax.n  in
                      (match uu____592 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____596,c) ->
                           let uu____618 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____618
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____621 ->
                           let uu____622 =
                             let uu____628 =
                               let uu____630 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____633 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____630 uu____633
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____628)
                              in
                           FStar_Errors.raise_error uu____622 r)
                  | uu____637 ->
                      let uu____638 =
                        let uu____644 =
                          let uu____646 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____649 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____646 uu____649
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____644)  in
                      FStar_Errors.raise_error uu____638 r
                   in
                ((let uu____654 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____660 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____660)
                     in
                  if uu____654
                  then
                    let uu____663 =
                      let uu____669 =
                        let uu____671 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____674 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____671 uu____674
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____669)
                       in
                    FStar_Errors.raise_error uu____663 r
                  else ());
                 (let uu____681 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____681 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____705 = fresh_a_and_u_a "a"  in
                      (match uu____705 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____731 = signature  in
                               match uu____731 with
                               | (us1,t,uu____746) -> (us1, t)  in
                             let uu____763 =
                               let uu____764 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____764
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____763
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____791 =
                               let uu____794 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____794
                                 (fun uu____807  ->
                                    match uu____807 with
                                    | (t,u1) ->
                                        let uu____814 =
                                          let uu____817 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____817
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____814)
                                in
                             FStar_Syntax_Util.arrow bs uu____791  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____820 =
                               let uu____833 =
                                 let uu____836 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____836
                                  in
                               (repr_us, repr_t, uu____833)  in
                             (uu____820, underlying_effect_lid))))))
             in
          match uu____508 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____909 = signature  in
                    match uu____909 with | (us,t,uu____924) -> (us, t)  in
                  let repr_ts =
                    let uu____942 = repr  in
                    match uu____942 with | (us,t,uu____957) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts repr_ts u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1007 =
                    let uu____1013 =
                      let uu____1015 = FStar_Util.string_of_int n1  in
                      let uu____1017 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1019 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1015 uu____1017 uu____1019
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1013)  in
                  FStar_Errors.raise_error uu____1007 r  in
                let return_repr =
                  let r =
                    (FStar_Pervasives_Native.snd
                       ed.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                     in
                  let uu____1049 =
                    check_and_gen "return_repr" Prims.int_one
                      ed.FStar_Syntax_Syntax.return_repr
                     in
                  match uu____1049 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1073 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1073 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1093 = fresh_a_and_u_a "a"  in
                           (match uu____1093 with
                            | (a,u_a) ->
                                let rest_bs =
                                  let uu____1122 =
                                    let uu____1123 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1123.FStar_Syntax_Syntax.n  in
                                  match uu____1122 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1135) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1163 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1163 with
                                       | (a',uu____1173)::bs1 ->
                                           let uu____1193 =
                                             let uu____1194 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - Prims.int_one))
                                                in
                                             FStar_All.pipe_right uu____1194
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____1292 =
                                             let uu____1305 =
                                               let uu____1308 =
                                                 let uu____1309 =
                                                   let uu____1316 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a)
                                                      in
                                                   (a', uu____1316)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1309
                                                  in
                                               [uu____1308]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1305
                                              in
                                           FStar_All.pipe_right uu____1193
                                             uu____1292)
                                  | uu____1331 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs =
                                  let uu____1343 =
                                    let uu____1352 =
                                      let uu____1361 = fresh_x_a "x" a  in
                                      [uu____1361]  in
                                    FStar_List.append rest_bs uu____1352  in
                                  a :: uu____1343  in
                                let uu____1393 =
                                  let uu____1398 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1399 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1398 u_a uu____1399  in
                                (match uu____1393 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1419 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1419
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1424 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1424);
                                      (let uu____1425 =
                                         let uu____1428 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1428
                                          in
                                       (ret_us, ret_t, uu____1425))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let r =
                     (FStar_Pervasives_Native.snd
                        ed.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                      in
                   let uu____1455 =
                     check_and_gen "bind_repr" (Prims.of_int (2))
                       ed.FStar_Syntax_Syntax.bind_repr
                      in
                   match uu____1455 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1479 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1479 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1499 = fresh_a_and_u_a "a"  in
                            (match uu____1499 with
                             | (a,u_a) ->
                                 let uu____1519 = fresh_a_and_u_a "b"  in
                                 (match uu____1519 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1548 =
                                          let uu____1549 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1549.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1548 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1561) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1589 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1589 with
                                             | (a',uu____1599)::(b',uu____1601)::bs1
                                                 ->
                                                 let uu____1631 =
                                                   let uu____1632 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1632
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1698 =
                                                   let uu____1711 =
                                                     let uu____1714 =
                                                       let uu____1715 =
                                                         let uu____1722 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1722)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1715
                                                        in
                                                     let uu____1729 =
                                                       let uu____1732 =
                                                         let uu____1733 =
                                                           let uu____1740 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1740)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1733
                                                          in
                                                       [uu____1732]  in
                                                     uu____1714 :: uu____1729
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1711
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1631 uu____1698)
                                        | uu____1755 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1779 =
                                        let uu____1790 =
                                          let uu____1795 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1796 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1795 u_a
                                            uu____1796
                                           in
                                        match uu____1790 with
                                        | (repr1,g) ->
                                            let uu____1811 =
                                              let uu____1818 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1818
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1811, g)
                                         in
                                      (match uu____1779 with
                                       | (f,guard_f) ->
                                           let uu____1858 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1871 =
                                               let uu____1876 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1895 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1876 u_b
                                                 uu____1895
                                                in
                                             match uu____1871 with
                                             | (repr1,g) ->
                                                 let uu____1910 =
                                                   let uu____1917 =
                                                     let uu____1918 =
                                                       let uu____1919 =
                                                         let uu____1922 =
                                                           let uu____1925 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1925
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____1922
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____1919
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____1918
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1917
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____1910, g)
                                              in
                                           (match uu____1858 with
                                            | (g,guard_g) ->
                                                let uu____1977 =
                                                  let uu____1982 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____1983 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____1982 u_b
                                                    uu____1983
                                                   in
                                                (match uu____1977 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2003 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2003
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
                                                      (let uu____2032 =
                                                         let uu____2035 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2035
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2032)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      FStar_All.pipe_right
                        ed.FStar_Syntax_Syntax.stronger_repr FStar_Util.must
                       in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2077 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2077 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2102 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2102
                          then
                            let uu____2107 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2113 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2107 uu____2113
                          else ());
                         (let uu____2122 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2122 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2142 = fresh_a_and_u_a "a"  in
                              (match uu____2142 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2171 =
                                       let uu____2172 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2172.FStar_Syntax_Syntax.n  in
                                     match uu____2171 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2184) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2212 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2212 with
                                          | (a',uu____2222)::bs1 ->
                                              let uu____2242 =
                                                let uu____2243 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2243
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2341 =
                                                let uu____2354 =
                                                  let uu____2357 =
                                                    let uu____2358 =
                                                      let uu____2365 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2365)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2358
                                                     in
                                                  [uu____2357]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2354
                                                 in
                                              FStar_All.pipe_right uu____2242
                                                uu____2341)
                                     | uu____2380 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2398 =
                                     let uu____2409 =
                                       let uu____2414 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2415 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2414 u uu____2415
                                        in
                                     match uu____2409 with
                                     | (repr1,g) ->
                                         let uu____2430 =
                                           let uu____2437 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2437
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2430, g)
                                      in
                                   (match uu____2398 with
                                    | (f,guard_f) ->
                                        let uu____2477 =
                                          let uu____2482 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2483 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2482 u
                                            uu____2483
                                           in
                                        (match uu____2477 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2502 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2502 FStar_Util.must
                                                  in
                                               let uu____2519 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2519 with
                                               | (uu____2524,pure_wp_t) ->
                                                   let uu____2526 =
                                                     let uu____2531 =
                                                       let uu____2532 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2532]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2531
                                                      in
                                                   uu____2526
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2565 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2581 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2581
                                                 pure_wp_t
                                                in
                                             (match uu____2565 with
                                              | (pure_wp_uvar,uu____2595,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2610 =
                                                      let uu____2611 =
                                                        let uu____2612 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2612]  in
                                                      let uu____2613 =
                                                        let uu____2624 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2624]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2611;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2613;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2610
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2679 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2679
                                                    then
                                                      let uu____2684 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2684
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
                                                     let uu____2692 =
                                                       let uu____2695 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2695
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2692))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2720 =
                         FStar_All.pipe_right
                           ed.FStar_Syntax_Syntax.match_wps FStar_Util.right
                          in
                       uu____2720.FStar_Syntax_Syntax.sif_then_else  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2730 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2730 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2754 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2754 with
                          | (us,t) ->
                              let uu____2773 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2773 with
                               | (uu____2790,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2793 = fresh_a_and_u_a "a"  in
                                   (match uu____2793 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2822 =
                                            let uu____2823 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2823.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2822 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2835) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2863 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2863 with
                                               | (a',uu____2873)::bs1 ->
                                                   let uu____2893 =
                                                     let uu____2894 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2894
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____2992 =
                                                     let uu____3005 =
                                                       let uu____3008 =
                                                         let uu____3009 =
                                                           let uu____3016 =
                                                             let uu____3019 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3019
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3016)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3009
                                                          in
                                                       [uu____3008]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3005
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2893 uu____2992)
                                          | uu____3040 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3058 =
                                          let uu____3069 =
                                            let uu____3074 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3075 =
                                              let uu____3076 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3076
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3074 u_a
                                              uu____3075
                                             in
                                          match uu____3069 with
                                          | (repr1,g) ->
                                              let uu____3097 =
                                                let uu____3104 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3104
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3097, g)
                                           in
                                        (match uu____3058 with
                                         | (f_bs,guard_f) ->
                                             let uu____3144 =
                                               let uu____3155 =
                                                 let uu____3160 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3161 =
                                                   let uu____3162 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3162
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3160 u_a
                                                   uu____3161
                                                  in
                                               match uu____3155 with
                                               | (repr1,g) ->
                                                   let uu____3183 =
                                                     let uu____3190 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3190
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3183, g)
                                                in
                                             (match uu____3144 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3237 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3237
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3245 =
                                                    let uu____3250 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3269 =
                                                      let uu____3270 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3270
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3250
                                                      u_a uu____3269
                                                     in
                                                  (match uu____3245 with
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
                                                        (let uu____3330 =
                                                           let uu____3333 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3333
                                                            in
                                                         (if_then_else_us,
                                                           uu____3330,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3344 =
                        let uu____3347 =
                          let uu____3356 =
                            FStar_All.pipe_right
                              ed.FStar_Syntax_Syntax.match_wps
                              FStar_Util.right
                             in
                          uu____3356.FStar_Syntax_Syntax.sif_then_else  in
                        FStar_All.pipe_right uu____3347
                          FStar_Pervasives_Native.snd
                         in
                      uu____3344.FStar_Syntax_Syntax.pos  in
                    let uu____3375 = if_then_else1  in
                    match uu____3375 with
                    | (ite_us,ite_t,uu____3390) ->
                        let uu____3403 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3403 with
                         | (us,ite_t1) ->
                             let uu____3410 =
                               let uu____3421 =
                                 let uu____3422 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3422.FStar_Syntax_Syntax.n  in
                               match uu____3421 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3436,uu____3437) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3463 =
                                     let uu____3476 =
                                       let uu____3481 =
                                         let uu____3484 =
                                           let uu____3493 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3493
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3484
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3481
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3476
                                       (fun l  ->
                                          let uu____3649 = l  in
                                          match uu____3649 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3463 with
                                    | (f,g,p) ->
                                        let uu____3714 =
                                          let uu____3715 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3715 bs1
                                           in
                                        let uu____3716 =
                                          let uu____3717 =
                                            let uu____3722 =
                                              let uu____3723 =
                                                let uu____3726 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3726
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3723
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3722
                                             in
                                          uu____3717
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3714, uu____3716, f, g, p))
                               | uu____3753 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3410 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3770 =
                                    let uu____3779 = stronger_repr  in
                                    match uu____3779 with
                                    | (uu____3800,subcomp_t,subcomp_ty) ->
                                        let uu____3815 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3815 with
                                         | (uu____3828,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3839 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3839 with
                                               | (uu____3852,subcomp_ty1) ->
                                                   let uu____3854 =
                                                     let uu____3855 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3855.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3854 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3867) ->
                                                        let uu____3888 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3888
                                                          FStar_Pervasives_Native.fst
                                                    | uu____3994 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4012 =
                                                 let uu____4017 =
                                                   let uu____4018 =
                                                     let uu____4021 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4041 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4021 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4018
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4017
                                                  in
                                               uu____4012
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4050 = aux f_t  in
                                             let uu____4053 = aux g_t  in
                                             (uu____4050, uu____4053))
                                     in
                                  (match uu____3770 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4070 =
                                         let aux t =
                                           let uu____4087 =
                                             let uu____4094 =
                                               let uu____4095 =
                                                 let uu____4122 =
                                                   let uu____4139 =
                                                     let uu____4148 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4148
                                                      in
                                                   (uu____4139,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4122,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4095
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4094
                                              in
                                           uu____4087
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4189 = aux subcomp_f  in
                                         let uu____4190 = aux subcomp_g  in
                                         (uu____4189, uu____4190)  in
                                       (match uu____4070 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4194 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4194
                                              then
                                                let uu____4199 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4201 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4199 uu____4201
                                              else ());
                                             (let uu____4206 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4206 with
                                              | (uu____4213,uu____4214,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4217 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4217 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4219 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4219 with
                                                    | (uu____4226,uu____4227,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4233 =
                                                              let uu____4238
                                                                =
                                                                let uu____4239
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4239
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4240
                                                                =
                                                                let uu____4241
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4241]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4238
                                                                uu____4240
                                                               in
                                                            uu____4233
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4274 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4274 g_g
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
                        (let uu____4298 =
                           let uu____4304 =
                             let uu____4306 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4306
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4304)
                            in
                         FStar_Errors.raise_error uu____4298 r)
                      else ();
                      (let uu____4313 =
                         let uu____4318 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4318 with
                         | (usubst,us) ->
                             let uu____4341 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4342 =
                               let uu___410_4343 = act  in
                               let uu____4344 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4345 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___410_4343.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___410_4343.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___410_4343.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4344;
                                 FStar_Syntax_Syntax.action_typ = uu____4345
                               }  in
                             (uu____4341, uu____4342)
                          in
                       match uu____4313 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4349 =
                               let uu____4350 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4350.FStar_Syntax_Syntax.n  in
                             match uu____4349 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4376 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4376
                                 then
                                   let repr_ts =
                                     let uu____4380 = repr  in
                                     match uu____4380 with
                                     | (us,t,uu____4395) -> (us, t)  in
                                   let repr1 =
                                     let uu____4413 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4413
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4425 =
                                       let uu____4430 =
                                         let uu____4431 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4431 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4430
                                        in
                                     uu____4425 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4449 =
                                       let uu____4452 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4452
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4449
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4455 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4456 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4456 with
                            | (act_typ1,uu____4464,g_t) ->
                                let uu____4466 =
                                  let uu____4473 =
                                    let uu___435_4474 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___435_4474.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___435_4474.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___435_4474.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___435_4474.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___435_4474.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___435_4474.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___435_4474.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___435_4474.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___435_4474.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___435_4474.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___435_4474.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___435_4474.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___435_4474.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___435_4474.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___435_4474.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___435_4474.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___435_4474.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___435_4474.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___435_4474.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___435_4474.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___435_4474.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___435_4474.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___435_4474.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___435_4474.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___435_4474.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___435_4474.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___435_4474.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___435_4474.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___435_4474.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___435_4474.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___435_4474.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___435_4474.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___435_4474.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___435_4474.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___435_4474.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___435_4474.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___435_4474.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___435_4474.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___435_4474.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___435_4474.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___435_4474.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___435_4474.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___435_4474.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___435_4474.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4473
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4466 with
                                 | (act_defn,uu____4477,g_d) ->
                                     ((let uu____4480 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4480
                                       then
                                         let uu____4485 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4487 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4485 uu____4487
                                       else ());
                                      (let uu____4492 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4500 =
                                           let uu____4501 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4501.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4500 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4511) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4534 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4534 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4550 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4550 with
                                                   | (a_tm,uu____4570,g_tm)
                                                       ->
                                                       let uu____4584 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4584 with
                                                        | (repr1,g) ->
                                                            let uu____4597 =
                                                              let uu____4600
                                                                =
                                                                let uu____4603
                                                                  =
                                                                  let uu____4606
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4606
                                                                    (
                                                                    fun _4609
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4609)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4603
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4600
                                                               in
                                                            let uu____4610 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4597,
                                                              uu____4610))))
                                         | uu____4613 ->
                                             let uu____4614 =
                                               let uu____4620 =
                                                 let uu____4622 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4622
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4620)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4614 r
                                          in
                                       match uu____4492 with
                                       | (k,g_k) ->
                                           ((let uu____4639 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4639
                                             then
                                               let uu____4644 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4644
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4652 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4652
                                              then
                                                let uu____4657 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4657
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4670 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4670
                                                   in
                                                let repr_args t =
                                                  let uu____4691 =
                                                    let uu____4692 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4692.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4691 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4744 =
                                                        let uu____4745 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4745.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4744 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4754,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4764 ->
                                                           let uu____4765 =
                                                             let uu____4771 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4771)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4765 r)
                                                  | uu____4780 ->
                                                      let uu____4781 =
                                                        let uu____4787 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4787)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4781 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4797 =
                                                  let uu____4798 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4798.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4797 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4823 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4823 with
                                                     | (bs1,c1) ->
                                                         let uu____4830 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4830
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
                                                              let uu____4841
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4841))
                                                | uu____4844 ->
                                                    let uu____4845 =
                                                      let uu____4851 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4851)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4845 r
                                                 in
                                              (let uu____4855 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4855
                                               then
                                                 let uu____4860 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4860
                                               else ());
                                              (let act2 =
                                                 let uu____4866 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4866 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___508_4880 =
                                                         act1  in
                                                       let uu____4881 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___508_4880.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___508_4880.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___508_4880.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4881
                                                       }
                                                     else
                                                       (let uu____4884 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4891
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4891
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4884
                                                        then
                                                          let uu___513_4896 =
                                                            act1  in
                                                          let uu____4897 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___513_4896.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___513_4896.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___513_4896.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___513_4896.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4897
                                                          }
                                                        else
                                                          (let uu____4900 =
                                                             let uu____4906 =
                                                               let uu____4908
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4910
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4908
                                                                 uu____4910
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4906)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4900 r))
                                                  in
                                               act2)))))))))
                       in
                    let fst1 uu____4933 =
                      match uu____4933 with | (a,uu____4949,uu____4950) -> a
                       in
                    let snd1 uu____4982 =
                      match uu____4982 with | (uu____4997,b,uu____4999) -> b
                       in
                    let thd uu____5031 =
                      match uu____5031 with | (uu____5046,uu____5047,c) -> c
                       in
                    let uu___531_5061 = ed  in
                    let uu____5062 =
                      FStar_All.pipe_right
                        ((fst1 stronger_repr), (snd1 stronger_repr))
                        (fun _5071  -> FStar_Pervasives_Native.Some _5071)
                       in
                    let uu____5072 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.is_layered =
                        (true,
                          (FStar_Pervasives_Native.Some underlying_effect_lid));
                      FStar_Syntax_Syntax.cattributes =
                        (uu___531_5061.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___531_5061.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___531_5061.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___531_5061.FStar_Syntax_Syntax.binders);
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
                             FStar_Syntax_Syntax.sif_then_else =
                               ((fst1 if_then_else1), (snd1 if_then_else1))
                           });
                      FStar_Syntax_Syntax.trivial =
                        (uu___531_5061.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                      FStar_Syntax_Syntax.return_repr =
                        ((fst1 return_repr), (snd1 return_repr));
                      FStar_Syntax_Syntax.bind_repr =
                        ((fst1 bind_repr), (snd1 bind_repr));
                      FStar_Syntax_Syntax.stronger_repr = uu____5062;
                      FStar_Syntax_Syntax.actions = uu____5072;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___531_5061.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5127 =
          FStar_TypeChecker_TcTerm.tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5127
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5149 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5149
         then
           let uu____5154 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5154
         else ());
        (let uu____5160 =
           let uu____5165 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5165 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5189 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5189  in
               let uu____5190 =
                 let uu____5197 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5197 bs  in
               (match uu____5190 with
                | (bs1,uu____5203,uu____5204) ->
                    let uu____5205 =
                      let tmp_t =
                        let uu____5215 =
                          let uu____5218 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5223  ->
                                 FStar_Pervasives_Native.Some _5223)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5218
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5215  in
                      let uu____5224 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5224 with
                      | (us,tmp_t1) ->
                          let uu____5241 =
                            let uu____5242 =
                              let uu____5243 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5243
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5242
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5241)
                       in
                    (match uu____5205 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5312 ->
                              let uu____5315 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5322 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5322 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5315
                              then (us, bs2)
                              else
                                (let uu____5333 =
                                   let uu____5339 =
                                     let uu____5341 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5343 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5341 uu____5343
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5339)
                                    in
                                 let uu____5347 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5333
                                   uu____5347))))
            in
         match uu____5160 with
         | (us,bs) ->
             let ed1 =
               let uu___564_5355 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___564_5355.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___564_5355.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___564_5355.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___564_5355.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___564_5355.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___564_5355.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___564_5355.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___564_5355.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___564_5355.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___564_5355.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___564_5355.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___564_5355.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___564_5355.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___564_5355.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___564_5355.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5356 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5356 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5375 =
                    let uu____5380 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5380  in
                  (match uu____5375 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5401 =
                           match uu____5401 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5421 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5421 t  in
                               let uu____5430 =
                                 let uu____5431 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5431 t1  in
                               (us1, uu____5430)
                            in
                         let uu___578_5436 = ed1  in
                         let uu____5437 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5438 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____5439 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____5440 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____5441 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____5446 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____5449 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____5450 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____5451 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____5452 =
                           FStar_List.map
                             (fun a  ->
                                let uu___581_5460 = a  in
                                let uu____5461 =
                                  let uu____5462 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5462  in
                                let uu____5473 =
                                  let uu____5474 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5474  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___581_5460.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___581_5460.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___581_5460.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___581_5460.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5461;
                                  FStar_Syntax_Syntax.action_typ = uu____5473
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___578_5436.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___578_5436.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___578_5436.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___578_5436.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___578_5436.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5437;
                           FStar_Syntax_Syntax.ret_wp = uu____5438;
                           FStar_Syntax_Syntax.bind_wp = uu____5439;
                           FStar_Syntax_Syntax.stronger = uu____5440;
                           FStar_Syntax_Syntax.match_wps = uu____5441;
                           FStar_Syntax_Syntax.trivial = uu____5446;
                           FStar_Syntax_Syntax.repr = uu____5449;
                           FStar_Syntax_Syntax.return_repr = uu____5450;
                           FStar_Syntax_Syntax.bind_repr = uu____5451;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____5452;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___578_5436.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5486 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5486
                         then
                           let uu____5491 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5491
                         else ());
                        (let env =
                           let uu____5498 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5498
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5533 k =
                           match uu____5533 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5553 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5553 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5562 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5562 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5563 =
                                            let uu____5570 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5570 t1
                                             in
                                          (match uu____5563 with
                                           | (t2,uu____5572,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5575 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5575 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5591 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5593 =
                                                 let uu____5595 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5595
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5591 uu____5593
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5610 ->
                                               let uu____5611 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5618 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5618 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5611
                                               then (g_us, t3)
                                               else
                                                 (let uu____5629 =
                                                    let uu____5635 =
                                                      let uu____5637 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5639 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5637
                                                        uu____5639
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5635)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5629
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5647 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5647
                          then
                            let uu____5652 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5652
                          else ());
                         (let fresh_a_and_wp uu____5668 =
                            let fail1 t =
                              let uu____5681 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5681
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5697 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5697 with
                            | (uu____5708,signature1) ->
                                let uu____5710 =
                                  let uu____5711 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5711.FStar_Syntax_Syntax.n  in
                                (match uu____5710 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5721) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5750)::(wp,uu____5752)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5781 -> fail1 signature1)
                                 | uu____5782 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5796 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5796
                            then
                              let uu____5801 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5801
                            else ()  in
                          let ret_wp =
                            let uu____5807 = fresh_a_and_wp ()  in
                            match uu____5807 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5823 =
                                    let uu____5832 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5839 =
                                      let uu____5848 =
                                        let uu____5855 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5855
                                         in
                                      [uu____5848]  in
                                    uu____5832 :: uu____5839  in
                                  let uu____5874 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5823
                                    uu____5874
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5882 = fresh_a_and_wp ()  in
                             match uu____5882 with
                             | (a,wp_sort_a) ->
                                 let uu____5895 = fresh_a_and_wp ()  in
                                 (match uu____5895 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5911 =
                                          let uu____5920 =
                                            let uu____5927 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5927
                                             in
                                          [uu____5920]  in
                                        let uu____5940 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5911
                                          uu____5940
                                         in
                                      let k =
                                        let uu____5946 =
                                          let uu____5955 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5962 =
                                            let uu____5971 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5978 =
                                              let uu____5987 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5994 =
                                                let uu____6003 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6010 =
                                                  let uu____6019 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6019]  in
                                                uu____6003 :: uu____6010  in
                                              uu____5987 :: uu____5994  in
                                            uu____5971 :: uu____5978  in
                                          uu____5955 :: uu____5962  in
                                        let uu____6062 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5946
                                          uu____6062
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6070 = fresh_a_and_wp ()  in
                              match uu____6070 with
                              | (a,wp_sort_a) ->
                                  let uu____6083 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6083 with
                                   | (t,uu____6089) ->
                                       let k =
                                         let uu____6093 =
                                           let uu____6102 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6109 =
                                             let uu____6118 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6125 =
                                               let uu____6134 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6134]  in
                                             uu____6118 :: uu____6125  in
                                           uu____6102 :: uu____6109  in
                                         let uu____6165 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6093
                                           uu____6165
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____6177 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____6177 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____6192 = fresh_a_and_wp ()  in
                                     match uu____6192 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____6206 =
                                             let uu____6209 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____6209
                                              in
                                           let uu____6210 =
                                             let uu____6211 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____6211
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____6206 uu____6210
                                            in
                                         let k =
                                           let uu____6223 =
                                             let uu____6232 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6239 =
                                               let uu____6248 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____6255 =
                                                 let uu____6264 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____6271 =
                                                   let uu____6280 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____6280]  in
                                                 uu____6264 :: uu____6271  in
                                               uu____6248 :: uu____6255  in
                                             uu____6232 :: uu____6239  in
                                           let uu____6317 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____6223
                                             uu____6317
                                            in
                                         check_and_gen' "if_then_else"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           if_then_else1
                                           (FStar_Pervasives_Native.Some k)
                                      in
                                   (log_combinator "if_then_else"
                                      if_then_else2;
                                    (let ite_wp1 =
                                       let uu____6325 = fresh_a_and_wp ()  in
                                       match uu____6325 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____6341 =
                                               let uu____6350 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6357 =
                                                 let uu____6366 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6366]  in
                                               uu____6350 :: uu____6357  in
                                             let uu____6391 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6341 uu____6391
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____6399 = fresh_a_and_wp ()
                                           in
                                        match uu____6399 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____6413 =
                                                let uu____6416 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6416
                                                 in
                                              let uu____6417 =
                                                let uu____6418 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____6418
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____6413 uu____6417
                                               in
                                            let wp_sort_b_a =
                                              let uu____6430 =
                                                let uu____6439 =
                                                  let uu____6446 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____6446
                                                   in
                                                [uu____6439]  in
                                              let uu____6459 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6430 uu____6459
                                               in
                                            let k =
                                              let uu____6465 =
                                                let uu____6474 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____6481 =
                                                  let uu____6490 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____6497 =
                                                    let uu____6506 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____6506]  in
                                                  uu____6490 :: uu____6497
                                                   in
                                                uu____6474 :: uu____6481  in
                                              let uu____6537 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6465 uu____6537
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
                                          FStar_Syntax_Syntax.ite_wp =
                                            ite_wp1;
                                          FStar_Syntax_Syntax.close_wp =
                                            close_wp1
                                        })))
                                in
                             let trivial =
                               let uu____6547 = fresh_a_and_wp ()  in
                               match uu____6547 with
                               | (a,wp_sort_a) ->
                                   let uu____6562 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____6562 with
                                    | (t,uu____6570) ->
                                        let k =
                                          let uu____6574 =
                                            let uu____6583 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6590 =
                                              let uu____6599 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____6599]  in
                                            uu____6583 :: uu____6590  in
                                          let uu____6624 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____6574
                                            uu____6624
                                           in
                                        let trivial =
                                          let uu____6628 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____6628
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____6643 =
                               let uu____6654 =
                                 let uu____6655 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____6655.FStar_Syntax_Syntax.n  in
                               match uu____6654 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____6674 ->
                                   let repr =
                                     let uu____6676 = fresh_a_and_wp ()  in
                                     match uu____6676 with
                                     | (a,wp_sort_a) ->
                                         let uu____6689 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____6689 with
                                          | (t,uu____6695) ->
                                              let k =
                                                let uu____6699 =
                                                  let uu____6708 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____6715 =
                                                    let uu____6724 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____6724]  in
                                                  uu____6708 :: uu____6715
                                                   in
                                                let uu____6749 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____6699 uu____6749
                                                 in
                                              check_and_gen' "repr"
                                                Prims.int_one
                                                FStar_Pervasives_Native.None
                                                ed2.FStar_Syntax_Syntax.repr
                                                (FStar_Pervasives_Native.Some
                                                   k))
                                      in
                                   (log_combinator "repr" repr;
                                    (let mk_repr' t wp =
                                       let uu____6769 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____6769 with
                                       | (uu____6776,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____6779 =
                                             let uu____6786 =
                                               let uu____6787 =
                                                 let uu____6804 =
                                                   let uu____6815 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6832 =
                                                     let uu____6843 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6843]  in
                                                   uu____6815 :: uu____6832
                                                    in
                                                 (repr2, uu____6804)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____6787
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____6786
                                              in
                                           uu____6779
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____6909 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____6909 wp  in
                                     let destruct_repr t =
                                       let uu____6924 =
                                         let uu____6925 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____6925.FStar_Syntax_Syntax.n  in
                                       match uu____6924 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____6936,(t1,uu____6938)::
                                            (wp,uu____6940)::[])
                                           -> (t1, wp)
                                       | uu____6999 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____7010 = fresh_a_and_wp ()  in
                                       match uu____7010 with
                                       | (a,uu____7018) ->
                                           let x_a =
                                             let uu____7024 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____7024
                                              in
                                           let res =
                                             let wp =
                                               let uu____7032 =
                                                 let uu____7037 =
                                                   let uu____7038 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7038
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____7047 =
                                                   let uu____7048 =
                                                     let uu____7057 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____7057
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____7066 =
                                                     let uu____7077 =
                                                       let uu____7086 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____7086
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____7077]  in
                                                   uu____7048 :: uu____7066
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____7037 uu____7047
                                                  in
                                               uu____7032
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____7122 =
                                               let uu____7131 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____7138 =
                                                 let uu____7147 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____7147]  in
                                               uu____7131 :: uu____7138  in
                                             let uu____7172 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____7122 uu____7172
                                              in
                                           let uu____7175 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____7175 with
                                            | (k1,uu____7183,uu____7184) ->
                                                let env1 =
                                                  let uu____7188 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____7188
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
                                          let uu____7199 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____7199
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____7200 = fresh_a_and_wp ()
                                           in
                                        match uu____7200 with
                                        | (a,wp_sort_a) ->
                                            let uu____7213 =
                                              fresh_a_and_wp ()  in
                                            (match uu____7213 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____7229 =
                                                     let uu____7238 =
                                                       let uu____7245 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____7245
                                                        in
                                                     [uu____7238]  in
                                                   let uu____7258 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7229 uu____7258
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
                                                   let uu____7266 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____7266
                                                    in
                                                 let wp_g_x =
                                                   let uu____7271 =
                                                     let uu____7276 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____7277 =
                                                       let uu____7278 =
                                                         let uu____7287 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7287
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____7278]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____7276 uu____7277
                                                      in
                                                   uu____7271
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____7318 =
                                                       let uu____7323 =
                                                         let uu____7324 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7324
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____7333 =
                                                         let uu____7334 =
                                                           let uu____7337 =
                                                             let uu____7340 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____7341 =
                                                               let uu____7344
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____7345
                                                                 =
                                                                 let uu____7348
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____7349
                                                                   =
                                                                   let uu____7352
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____7352]
                                                                    in
                                                                 uu____7348
                                                                   ::
                                                                   uu____7349
                                                                  in
                                                               uu____7344 ::
                                                                 uu____7345
                                                                in
                                                             uu____7340 ::
                                                               uu____7341
                                                              in
                                                           r :: uu____7337
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7334
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____7323
                                                         uu____7333
                                                        in
                                                     uu____7318
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____7370 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____7370
                                                   then
                                                     let uu____7381 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____7388 =
                                                       let uu____7397 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____7397]  in
                                                     uu____7381 :: uu____7388
                                                   else []  in
                                                 let k =
                                                   let uu____7433 =
                                                     let uu____7442 =
                                                       let uu____7451 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____7458 =
                                                         let uu____7467 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____7467]  in
                                                       uu____7451 ::
                                                         uu____7458
                                                        in
                                                     let uu____7492 =
                                                       let uu____7501 =
                                                         let uu____7510 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____7517 =
                                                           let uu____7526 =
                                                             let uu____7533 =
                                                               let uu____7534
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____7534
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____7533
                                                              in
                                                           let uu____7535 =
                                                             let uu____7544 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____7551 =
                                                               let uu____7560
                                                                 =
                                                                 let uu____7567
                                                                   =
                                                                   let uu____7568
                                                                    =
                                                                    let uu____7577
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7577]
                                                                     in
                                                                   let uu____7596
                                                                    =
                                                                    let uu____7599
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7599
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____7568
                                                                    uu____7596
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____7567
                                                                  in
                                                               [uu____7560]
                                                                in
                                                             uu____7544 ::
                                                               uu____7551
                                                              in
                                                           uu____7526 ::
                                                             uu____7535
                                                            in
                                                         uu____7510 ::
                                                           uu____7517
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____7501
                                                        in
                                                     FStar_List.append
                                                       uu____7442 uu____7492
                                                      in
                                                   let uu____7644 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7433 uu____7644
                                                    in
                                                 let uu____7647 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____7647 with
                                                  | (k1,uu____7655,uu____7656)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___779_7668
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___779_7668.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _7670  ->
                                                             FStar_Pervasives_Native.Some
                                                               _7670)
                                                         in
                                                      check_and_gen'
                                                        "bind_repr"
                                                        (Prims.of_int (2))
                                                        env2
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
                                           (let uu____7697 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____7711 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____7711 with
                                                 | (usubst,uvs) ->
                                                     let uu____7734 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____7735 =
                                                       let uu___792_7736 =
                                                         act  in
                                                       let uu____7737 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____7738 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___792_7736.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___792_7736.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___792_7736.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____7737;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7738
                                                       }  in
                                                     (uu____7734, uu____7735))
                                               in
                                            match uu____7697 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____7742 =
                                                    let uu____7743 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____7743.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____7742 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____7769 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____7769
                                                      then
                                                        let uu____7772 =
                                                          let uu____7775 =
                                                            let uu____7776 =
                                                              let uu____7777
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____7777
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____7776
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____7775
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____7772
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____7800 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____7801 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____7801 with
                                                 | (act_typ1,uu____7809,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___809_7812 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___809_7812.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____7815 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____7815
                                                       then
                                                         let uu____7819 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____7821 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____7823 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____7819
                                                           uu____7821
                                                           uu____7823
                                                       else ());
                                                      (let uu____7828 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____7828 with
                                                       | (act_defn,uu____7836,g_a)
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
                                                           let uu____7840 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____7876
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____7876
                                                                  with
                                                                  | (bs2,uu____7888)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7895
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7895
                                                                     in
                                                                    let uu____7898
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7898
                                                                    with
                                                                    | 
                                                                    (k1,uu____7912,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____7916 ->
                                                                 let uu____7917
                                                                   =
                                                                   let uu____7923
                                                                    =
                                                                    let uu____7925
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7927
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7925
                                                                    uu____7927
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7923)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____7917
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____7840
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____7945
                                                                    =
                                                                    let uu____7946
                                                                    =
                                                                    let uu____7947
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7947
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7946
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____7945);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____7949
                                                                    =
                                                                    let uu____7950
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7950.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____7949
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7975
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7975
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7982
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7982
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8002
                                                                    =
                                                                    let uu____8003
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8003]
                                                                     in
                                                                    let uu____8004
                                                                    =
                                                                    let uu____8015
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8015]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8002;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8004;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8040
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8040))
                                                                    | 
                                                                    uu____8043
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____8045
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8067
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8067))
                                                                     in
                                                                  match uu____8045
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
                                                                    let uu___859_8086
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___859_8086.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___859_8086.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___859_8086.FStar_Syntax_Syntax.action_params);
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
                                       (repr, return_repr, bind_repr,
                                         actions)))))
                                in
                             match uu____6643 with
                             | (repr,return_repr,bind_repr,actions) ->
                                 let cl ts =
                                   let ts1 =
                                     FStar_Syntax_Subst.close_tscheme ed_bs
                                       ts
                                      in
                                   let ed_univs_closing =
                                     FStar_Syntax_Subst.univ_var_closing
                                       ed_univs
                                      in
                                   let uu____8111 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____8111 ts1
                                    in
                                 let ed3 =
                                   let uu___871_8121 = ed2  in
                                   let uu____8122 = cl signature  in
                                   let uu____8123 = cl ret_wp  in
                                   let uu____8124 = cl bind_wp  in
                                   let uu____8125 = cl stronger  in
                                   let uu____8126 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____8131 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____8134 = cl repr  in
                                   let uu____8135 = cl return_repr  in
                                   let uu____8136 = cl bind_repr  in
                                   let uu____8137 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___874_8145 = a  in
                                          let uu____8146 =
                                            let uu____8147 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____8147
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____8172 =
                                            let uu____8173 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____8173
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___874_8145.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___874_8145.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___874_8145.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___874_8145.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____8146;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____8172
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___871_8121.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___871_8121.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___871_8121.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___871_8121.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___871_8121.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____8122;
                                     FStar_Syntax_Syntax.ret_wp = uu____8123;
                                     FStar_Syntax_Syntax.bind_wp = uu____8124;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____8125;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____8126;
                                     FStar_Syntax_Syntax.trivial = uu____8131;
                                     FStar_Syntax_Syntax.repr = uu____8134;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____8135;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____8136;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____8137;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___871_8121.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____8199 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____8199
                                   then
                                     let uu____8204 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____8204
                                   else ());
                                  ed3))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      fun quals  ->
        (if FStar_Pervasives_Native.fst ed.FStar_Syntax_Syntax.is_layered
         then tc_layered_eff_decl
         else tc_non_layered_eff_decl) env ed quals
  
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
        let fail1 uu____8269 =
          let uu____8270 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8276 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8270 uu____8276  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8320)::(wp,uu____8322)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8351 -> fail1 ())
        | uu____8352 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8365 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8365
       then
         let uu____8370 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8370
       else ());
      (let uu____8375 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8375 with
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
             let uu____8408 =
               ((FStar_Pervasives_Native.fst
                   src_ed.FStar_Syntax_Syntax.is_layered)
                  &&
                  (let uu____8414 =
                     let uu____8415 =
                       FStar_All.pipe_right
                         src_ed.FStar_Syntax_Syntax.is_layered
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____8415 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8414
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_Pervasives_Native.fst
                      tgt_ed.FStar_Syntax_Syntax.is_layered)
                     &&
                     (let uu____8436 =
                        let uu____8437 =
                          FStar_All.pipe_right
                            tgt_ed.FStar_Syntax_Syntax.is_layered
                            FStar_Pervasives_Native.snd
                           in
                        FStar_All.pipe_right uu____8437 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8436
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8455 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8455))
                in
             if uu____8408
             then
               let uu____8458 =
                 let uu____8464 =
                   let uu____8466 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8469 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8466 uu____8469
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8464)  in
               FStar_Errors.raise_error uu____8458 r
             else ());
            (let uu____8476 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8500 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8500 with
                  | (us1,lift1) ->
                      let uu____8515 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8515, us1, lift1))
                in
             match uu____8476 with
             | (env,us1,lift1) ->
                 let uu____8525 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8525 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8538 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8538
                         then
                           let uu____8543 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8545 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8543 uu____8545
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8559 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8561 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8563 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8559 uu____8561 s uu____8563
                            in
                         let uu____8566 =
                           let uu____8573 =
                             let uu____8578 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8578
                               (fun uu____8595  ->
                                  match uu____8595 with
                                  | (t,u) ->
                                      let uu____8606 =
                                        let uu____8607 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8607
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8606, u))
                              in
                           match uu____8573 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8626 =
                                   let uu____8627 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8627.FStar_Syntax_Syntax.n  in
                                 match uu____8626 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8639) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8667 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8667 with
                                      | (a',uu____8677)::bs1 ->
                                          let uu____8697 =
                                            let uu____8698 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8698
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8796 =
                                            let uu____8809 =
                                              let uu____8812 =
                                                let uu____8813 =
                                                  let uu____8820 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8820)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8813
                                                 in
                                              [uu____8812]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8809
                                             in
                                          FStar_All.pipe_right uu____8697
                                            uu____8796)
                                 | uu____8835 ->
                                     let uu____8836 =
                                       let uu____8842 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____8842)
                                        in
                                     FStar_Errors.raise_error uu____8836 r
                                  in
                               let uu____8854 =
                                 let uu____8865 =
                                   let uu____8870 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____8877 =
                                     let uu____8878 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8878
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____8870 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____8877
                                    in
                                 match uu____8865 with
                                 | (f_sort,g1) ->
                                     let uu____8899 =
                                       let uu____8906 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____8906
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____8899, g1)
                                  in
                               (match uu____8854 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____8973 =
                                      let uu____8978 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____8979 =
                                        let uu____8980 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____8980
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____8978 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____8979
                                       in
                                    (match uu____8973 with
                                     | (repr,g_repr) ->
                                         let uu____8997 =
                                           let uu____9000 =
                                             let uu____9003 =
                                               let uu____9006 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9006
                                                 (fun _9009  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9009)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9003
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9000
                                            in
                                         let uu____9010 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____8997, uu____9010)))
                            in
                         match uu____8566 with
                         | (k,g_k) ->
                             ((let uu____9020 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9020
                               then
                                 let uu____9025 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9025
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9034 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9034
                                then
                                  let uu____9039 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9039
                                else ());
                               (let uu____9044 =
                                  let uu____9057 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9057 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9084 =
                                            let uu____9090 =
                                              let uu____9092 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9094 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9096 =
                                                let uu____9098 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9098
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9105 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9092 uu____9094
                                                uu____9096 uu____9105
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9090)
                                             in
                                          FStar_Errors.raise_error uu____9084
                                            r)
                                       else ();
                                       (let uu____9111 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9120 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9120 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9111
                                        then
                                          let uu____9137 =
                                            let uu____9140 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9140
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9137)
                                        else
                                          (let uu____9151 =
                                             let uu____9157 =
                                               let uu____9159 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9161 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9163 =
                                                 let uu____9165 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9165
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9172 =
                                                 let uu____9174 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9174
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9181 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9159 uu____9161
                                                 uu____9163 uu____9172
                                                 uu____9181
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9157)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9151 r)))
                                   in
                                match uu____9044 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___982_9213 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___982_9213.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___982_9213.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9223 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9223
                                      then
                                        let uu____9228 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9228
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
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        if
          (FStar_Pervasives_Native.fst ed_src.FStar_Syntax_Syntax.is_layered)
            ||
            (FStar_Pervasives_Native.fst
               ed_tgt.FStar_Syntax_Syntax.is_layered)
        then tc_layered_lift env sub1
        else
          (let uu____9260 =
             let uu____9267 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9267
              in
           match uu____9260 with
           | (a,wp_a_src) ->
               let uu____9274 =
                 let uu____9281 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9281
                  in
               (match uu____9274 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9289 =
                        let uu____9292 =
                          let uu____9293 =
                            let uu____9300 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9300)  in
                          FStar_Syntax_Syntax.NT uu____9293  in
                        [uu____9292]  in
                      FStar_Syntax_Subst.subst uu____9289 wp_b_tgt  in
                    let expected_k =
                      let uu____9308 =
                        let uu____9317 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9324 =
                          let uu____9333 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9333]  in
                        uu____9317 :: uu____9324  in
                      let uu____9358 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9308 uu____9358  in
                    let repr_type eff_name a1 wp =
                      (let uu____9380 =
                         let uu____9382 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9382  in
                       if uu____9380
                       then
                         let uu____9385 =
                           let uu____9391 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9391)
                            in
                         let uu____9395 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9385 uu____9395
                       else ());
                      (let uu____9398 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9398 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____9431 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9432 =
                             let uu____9439 =
                               let uu____9440 =
                                 let uu____9457 =
                                   let uu____9468 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9477 =
                                     let uu____9488 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9488]  in
                                   uu____9468 :: uu____9477  in
                                 (repr, uu____9457)  in
                               FStar_Syntax_Syntax.Tm_app uu____9440  in
                             FStar_Syntax_Syntax.mk uu____9439  in
                           uu____9432 FStar_Pervasives_Native.None uu____9431)
                       in
                    let uu____9533 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9706 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9717 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9717 with
                              | (usubst,uvs1) ->
                                  let uu____9740 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9741 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9740, uu____9741)
                            else (env, lift_wp)  in
                          (match uu____9706 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9791 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9791))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9862 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9877 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9877 with
                              | (usubst,uvs) ->
                                  let uu____9902 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9902)
                            else ([], lift)  in
                          (match uu____9862 with
                           | (uvs,lift1) ->
                               ((let uu____9938 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9938
                                 then
                                   let uu____9942 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9942
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9948 =
                                   let uu____9955 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9955 lift1
                                    in
                                 match uu____9948 with
                                 | (lift2,comp,uu____9980) ->
                                     let uu____9981 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____9981 with
                                      | (uu____10010,lift_wp,lift_elab) ->
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
                                            let uu____10042 =
                                              let uu____10053 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10053
                                               in
                                            let uu____10070 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10042, uu____10070)
                                          else
                                            (let uu____10099 =
                                               let uu____10110 =
                                                 let uu____10119 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10119)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10110
                                                in
                                             let uu____10134 =
                                               let uu____10143 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10143)  in
                                             (uu____10099, uu____10134))))))
                       in
                    (match uu____9533 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1062_10207 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1062_10207.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1062_10207.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1062_10207.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1062_10207.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1062_10207.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1062_10207.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1062_10207.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1062_10207.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1062_10207.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1062_10207.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1062_10207.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1062_10207.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1062_10207.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1062_10207.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1062_10207.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1062_10207.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1062_10207.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1062_10207.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1062_10207.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1062_10207.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1062_10207.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1062_10207.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1062_10207.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1062_10207.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1062_10207.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1062_10207.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1062_10207.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1062_10207.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1062_10207.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1062_10207.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1062_10207.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1062_10207.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1062_10207.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1062_10207.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1062_10207.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1062_10207.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1062_10207.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1062_10207.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1062_10207.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1062_10207.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1062_10207.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1062_10207.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1062_10207.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1062_10207.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10240 =
                                 let uu____10245 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10245 with
                                 | (usubst,uvs1) ->
                                     let uu____10268 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10269 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10268, uu____10269)
                                  in
                               (match uu____10240 with
                                | (env2,lift2) ->
                                    let uu____10274 =
                                      let uu____10281 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10281
                                       in
                                    (match uu____10274 with
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
                                             let uu____10307 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10308 =
                                               let uu____10315 =
                                                 let uu____10316 =
                                                   let uu____10333 =
                                                     let uu____10344 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10353 =
                                                       let uu____10364 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10364]  in
                                                     uu____10344 ::
                                                       uu____10353
                                                      in
                                                   (lift_wp1, uu____10333)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10316
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10315
                                                in
                                             uu____10308
                                               FStar_Pervasives_Native.None
                                               uu____10307
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10412 =
                                             let uu____10421 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10428 =
                                               let uu____10437 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10444 =
                                                 let uu____10453 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10453]  in
                                               uu____10437 :: uu____10444  in
                                             uu____10421 :: uu____10428  in
                                           let uu____10484 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10412 uu____10484
                                            in
                                         let uu____10487 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10487 with
                                          | (expected_k2,uu____10497,uu____10498)
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
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10506 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10506))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10514 =
                             let uu____10516 =
                               let uu____10518 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10518
                                 FStar_List.length
                                in
                             uu____10516 <> Prims.int_one  in
                           if uu____10514
                           then
                             let uu____10541 =
                               let uu____10547 =
                                 let uu____10549 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10551 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10553 =
                                   let uu____10555 =
                                     let uu____10557 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10557
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10555
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10549 uu____10551 uu____10553
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10547)
                                in
                             FStar_Errors.raise_error uu____10541 r
                           else ());
                          (let uu____10584 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10587 =
                                  let uu____10589 =
                                    let uu____10592 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10592
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10589
                                    FStar_List.length
                                   in
                                uu____10587 <> Prims.int_one)
                              in
                           if uu____10584
                           then
                             let uu____10630 =
                               let uu____10636 =
                                 let uu____10638 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10640 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10642 =
                                   let uu____10644 =
                                     let uu____10646 =
                                       let uu____10649 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10649
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10646
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10644
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10638 uu____10640 uu____10642
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10636)
                                in
                             FStar_Errors.raise_error uu____10630 r
                           else ());
                          (let uu___1099_10691 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1099_10691.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1099_10691.FStar_Syntax_Syntax.target);
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
    fun uu____10722  ->
      fun r  ->
        match uu____10722 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10745 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10773 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10773 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10804 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10804 c  in
                     let uu____10813 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10813, uvs1, tps1, c1))
               in
            (match uu____10745 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10833 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10833 with
                  | (tps2,c2) ->
                      let uu____10848 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10848 with
                       | (tps3,env3,us) ->
                           let uu____10866 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10866 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10892)::uu____10893 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10912 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10920 =
                                    let uu____10922 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10922  in
                                  if uu____10920
                                  then
                                    let uu____10925 =
                                      let uu____10931 =
                                        let uu____10933 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10935 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10933 uu____10935
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10931)
                                       in
                                    FStar_Errors.raise_error uu____10925 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10943 =
                                    let uu____10944 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10944
                                     in
                                  match uu____10943 with
                                  | (uvs2,t) ->
                                      let uu____10973 =
                                        let uu____10978 =
                                          let uu____10991 =
                                            let uu____10992 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____10992.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____10991)  in
                                        match uu____10978 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11007,c5)) -> ([], c5)
                                        | (uu____11049,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11088 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____10973 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11120 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11120 with
                                               | (uu____11125,t1) ->
                                                   let uu____11127 =
                                                     let uu____11133 =
                                                       let uu____11135 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11137 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11141 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11135
                                                         uu____11137
                                                         uu____11141
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11133)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11127 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  