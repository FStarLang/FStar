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
                                                 let uu____1730 =
                                                   let uu____1743 =
                                                     let uu____1746 =
                                                       let uu____1747 =
                                                         let uu____1754 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1754)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1747
                                                        in
                                                     let uu____1761 =
                                                       let uu____1764 =
                                                         let uu____1765 =
                                                           let uu____1772 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1772)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1765
                                                          in
                                                       [uu____1764]  in
                                                     uu____1746 :: uu____1761
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1743
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1631 uu____1730)
                                        | uu____1787 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1811 =
                                        let uu____1822 =
                                          let uu____1827 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1828 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1827 u_a
                                            uu____1828
                                           in
                                        match uu____1822 with
                                        | (repr1,g) ->
                                            let uu____1843 =
                                              let uu____1850 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1850
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1843, g)
                                         in
                                      (match uu____1811 with
                                       | (f,guard_f) ->
                                           let uu____1890 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1903 =
                                               let uu____1908 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1927 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1908 u_b
                                                 uu____1927
                                                in
                                             match uu____1903 with
                                             | (repr1,g) ->
                                                 let uu____1942 =
                                                   let uu____1949 =
                                                     let uu____1950 =
                                                       let uu____1951 =
                                                         let uu____1954 =
                                                           let uu____1957 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____1957
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____1954
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____1951
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____1950
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1949
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____1942, g)
                                              in
                                           (match uu____1890 with
                                            | (g,guard_g) ->
                                                let uu____2009 =
                                                  let uu____2014 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2015 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2014 u_b
                                                    uu____2015
                                                   in
                                                (match uu____2009 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2035 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2035
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
                                                      (let uu____2064 =
                                                         let uu____2067 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2067
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2064)))))))))
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
                    let uu____2109 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2109 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2134 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2134
                          then
                            let uu____2139 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2145 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2139 uu____2145
                          else ());
                         (let uu____2154 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2154 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2174 = fresh_a_and_u_a "a"  in
                              (match uu____2174 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2203 =
                                       let uu____2204 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2204.FStar_Syntax_Syntax.n  in
                                     match uu____2203 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2216) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2244 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2244 with
                                          | (a',uu____2254)::bs1 ->
                                              let uu____2274 =
                                                let uu____2275 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2275
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2373 =
                                                let uu____2386 =
                                                  let uu____2389 =
                                                    let uu____2390 =
                                                      let uu____2397 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2397)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2390
                                                     in
                                                  [uu____2389]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2386
                                                 in
                                              FStar_All.pipe_right uu____2274
                                                uu____2373)
                                     | uu____2412 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2430 =
                                     let uu____2441 =
                                       let uu____2446 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2447 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2446 u uu____2447
                                        in
                                     match uu____2441 with
                                     | (repr1,g) ->
                                         let uu____2462 =
                                           let uu____2469 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2469
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2462, g)
                                      in
                                   (match uu____2430 with
                                    | (f,guard_f) ->
                                        let uu____2509 =
                                          let uu____2514 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2515 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2514 u
                                            uu____2515
                                           in
                                        (match uu____2509 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2534 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2534 FStar_Util.must
                                                  in
                                               let uu____2551 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2551 with
                                               | (uu____2556,pure_wp_t) ->
                                                   let uu____2558 =
                                                     let uu____2563 =
                                                       let uu____2564 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2564]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2563
                                                      in
                                                   uu____2558
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2597 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2613 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2613
                                                 pure_wp_t
                                                in
                                             (match uu____2597 with
                                              | (pure_wp_uvar,uu____2627,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2642 =
                                                      let uu____2643 =
                                                        let uu____2644 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2644]  in
                                                      let uu____2645 =
                                                        let uu____2656 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2656]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2643;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2645;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2642
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2711 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2711
                                                    then
                                                      let uu____2716 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2716
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
                                                     let uu____2724 =
                                                       let uu____2727 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2727
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2724))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2752 =
                         FStar_All.pipe_right
                           ed.FStar_Syntax_Syntax.match_wps FStar_Util.right
                          in
                       uu____2752.FStar_Syntax_Syntax.sif_then_else  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2762 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2762 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2786 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2786 with
                          | (us,t) ->
                              let uu____2805 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2805 with
                               | (uu____2822,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2825 = fresh_a_and_u_a "a"  in
                                   (match uu____2825 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2854 =
                                            let uu____2855 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2855.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2854 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2867) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2895 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2895 with
                                               | (a',uu____2905)::bs1 ->
                                                   let uu____2925 =
                                                     let uu____2926 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____2926
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3024 =
                                                     let uu____3037 =
                                                       let uu____3040 =
                                                         let uu____3041 =
                                                           let uu____3048 =
                                                             let uu____3051 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3051
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3048)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3041
                                                          in
                                                       [uu____3040]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3037
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2925 uu____3024)
                                          | uu____3072 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3090 =
                                          let uu____3101 =
                                            let uu____3106 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3107 =
                                              let uu____3108 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3108
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3106 u_a
                                              uu____3107
                                             in
                                          match uu____3101 with
                                          | (repr1,g) ->
                                              let uu____3129 =
                                                let uu____3136 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3136
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3129, g)
                                           in
                                        (match uu____3090 with
                                         | (f_bs,guard_f) ->
                                             let uu____3176 =
                                               let uu____3187 =
                                                 let uu____3192 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3193 =
                                                   let uu____3194 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3194
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3192 u_a
                                                   uu____3193
                                                  in
                                               match uu____3187 with
                                               | (repr1,g) ->
                                                   let uu____3215 =
                                                     let uu____3222 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3222
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3215, g)
                                                in
                                             (match uu____3176 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3269 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3269
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3277 =
                                                    let uu____3282 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3301 =
                                                      let uu____3302 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3302
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3282
                                                      u_a uu____3301
                                                     in
                                                  (match uu____3277 with
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
                                                        (let uu____3362 =
                                                           let uu____3365 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3365
                                                            in
                                                         (if_then_else_us,
                                                           uu____3362,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3376 =
                        let uu____3379 =
                          let uu____3388 =
                            FStar_All.pipe_right
                              ed.FStar_Syntax_Syntax.match_wps
                              FStar_Util.right
                             in
                          uu____3388.FStar_Syntax_Syntax.sif_then_else  in
                        FStar_All.pipe_right uu____3379
                          FStar_Pervasives_Native.snd
                         in
                      uu____3376.FStar_Syntax_Syntax.pos  in
                    let uu____3407 = if_then_else1  in
                    match uu____3407 with
                    | (ite_us,ite_t,uu____3422) ->
                        let uu____3435 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3435 with
                         | (us,ite_t1) ->
                             let uu____3442 =
                               let uu____3461 =
                                 let uu____3462 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3462.FStar_Syntax_Syntax.n  in
                               match uu____3461 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3484,uu____3485) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3511 =
                                     let uu____3528 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.splitAt
                                            ((FStar_List.length bs1) -
                                               (Prims.of_int (3))))
                                        in
                                     FStar_All.pipe_right uu____3528
                                       (fun uu____3630  ->
                                          match uu____3630 with
                                          | (l1,l2) ->
                                              let uu____3701 =
                                                let uu____3704 =
                                                  FStar_All.pipe_right l2
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3704
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3701
                                                (fun l  ->
                                                   let uu____3755 = l  in
                                                   match uu____3755 with
                                                   | f::g::p::[] ->
                                                       (l1, f, g, p)))
                                      in
                                   (match uu____3511 with
                                    | (rest_bs,f,g,p) ->
                                        let uu____3823 =
                                          let uu____3824 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3824 bs1
                                           in
                                        (uu____3823, rest_bs, f, g, p))
                               | uu____3833 -> failwith "Impossible!"  in
                             (match uu____3442 with
                              | (env,ite_rest_bs,f_t,g_t,p_t) ->
                                  let subcomp_f =
                                    let uu____3877 = stronger_repr  in
                                    match uu____3877 with
                                    | (uu____3892,subcomp_t,subcomp_ty) ->
                                        let uu____3907 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3907 with
                                         | (uu____3914,subcomp_t1) ->
                                             let uu____3916 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us subcomp_ty
                                                in
                                             (match uu____3916 with
                                              | (uu____3923,subcomp_ty1) ->
                                                  let bs_except_f =
                                                    let uu____3934 =
                                                      let uu____3935 =
                                                        FStar_Syntax_Subst.compress
                                                          subcomp_ty1
                                                         in
                                                      uu____3935.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____3934 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3947) ->
                                                        let uu____3968 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3968
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4074 ->
                                                        failwith
                                                          "Impossible!"
                                                     in
                                                  let uu____4084 =
                                                    let uu____4089 =
                                                      let uu____4090 =
                                                        let uu____4093 =
                                                          FStar_All.pipe_right
                                                            bs_except_f
                                                            (FStar_List.map
                                                               (fun
                                                                  uu____4113 
                                                                  ->
                                                                  FStar_Syntax_Syntax.tun))
                                                           in
                                                        FStar_List.append
                                                          uu____4093 
                                                          [f_t]
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____4090
                                                        (FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg)
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      subcomp_t1 uu____4089
                                                     in
                                                  uu____4084
                                                    FStar_Pervasives_Native.None
                                                    r))
                                     in
                                  let ite_f_g =
                                    let uu____4125 =
                                      let uu____4130 =
                                        let uu____4131 =
                                          let uu____4134 =
                                            FStar_All.pipe_right ite_rest_bs
                                              (FStar_List.map
                                                 (fun uu____4154  ->
                                                    FStar_Syntax_Syntax.tun))
                                             in
                                          FStar_List.append uu____4134
                                            [f_t; g_t; p_t]
                                           in
                                        FStar_All.pipe_right uu____4131
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg)
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                        uu____4130
                                       in
                                    uu____4125 FStar_Pervasives_Native.None r
                                     in
                                  let tm_subcomp_ascribed =
                                    let uu____4166 =
                                      let uu____4173 =
                                        let uu____4174 =
                                          let uu____4201 =
                                            let uu____4218 =
                                              let uu____4227 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_f_g
                                                 in
                                              FStar_Util.Inr uu____4227  in
                                            (uu____4218,
                                              FStar_Pervasives_Native.None)
                                             in
                                          (subcomp_f, uu____4201,
                                            FStar_Pervasives_Native.None)
                                           in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____4174
                                         in
                                      FStar_Syntax_Syntax.mk uu____4173  in
                                    uu____4166 FStar_Pervasives_Native.None r
                                     in
                                  let env_with_p =
                                    let t =
                                      let uu____4270 =
                                        FStar_Syntax_Syntax.lid_as_fv
                                          FStar_Parser_Const.squash_lid
                                          FStar_Syntax_Syntax.delta_constant
                                          FStar_Pervasives_Native.None
                                         in
                                      FStar_All.pipe_right uu____4270
                                        FStar_Syntax_Syntax.fv_to_tm
                                       in
                                    let b =
                                      let uu____4272 =
                                        let uu____4273 =
                                          let uu____4278 =
                                            let uu____4279 =
                                              FStar_Syntax_Syntax.as_arg p_t
                                               in
                                            [uu____4279]  in
                                          FStar_Syntax_Syntax.mk_Tm_app t
                                            uu____4278
                                           in
                                        uu____4273
                                          FStar_Pervasives_Native.None r
                                         in
                                      FStar_Syntax_Syntax.null_binder
                                        uu____4272
                                       in
                                    FStar_TypeChecker_Env.push_binders env
                                      [b]
                                     in
                                  ())));
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
                        (let uu____4339 =
                           let uu____4345 =
                             let uu____4347 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4347
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4345)
                            in
                         FStar_Errors.raise_error uu____4339 r)
                      else ();
                      (let uu____4354 =
                         let uu____4359 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4359 with
                         | (usubst,us) ->
                             let uu____4382 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4383 =
                               let uu___397_4384 = act  in
                               let uu____4385 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4386 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___397_4384.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___397_4384.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___397_4384.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4385;
                                 FStar_Syntax_Syntax.action_typ = uu____4386
                               }  in
                             (uu____4382, uu____4383)
                          in
                       match uu____4354 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4390 =
                               let uu____4391 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4391.FStar_Syntax_Syntax.n  in
                             match uu____4390 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4417 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4417
                                 then
                                   let repr_ts =
                                     let uu____4421 = repr  in
                                     match uu____4421 with
                                     | (us,t,uu____4436) -> (us, t)  in
                                   let repr1 =
                                     let uu____4454 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4454
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4466 =
                                       let uu____4471 =
                                         let uu____4472 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4472 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4471
                                        in
                                     uu____4466 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4490 =
                                       let uu____4493 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4493
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4490
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4496 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4497 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4497 with
                            | (act_typ1,uu____4505,g_t) ->
                                let uu____4507 =
                                  let uu____4514 =
                                    let uu___422_4515 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___422_4515.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___422_4515.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___422_4515.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___422_4515.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___422_4515.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___422_4515.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___422_4515.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___422_4515.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___422_4515.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___422_4515.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___422_4515.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___422_4515.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___422_4515.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___422_4515.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___422_4515.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___422_4515.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___422_4515.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___422_4515.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___422_4515.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___422_4515.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___422_4515.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___422_4515.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___422_4515.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___422_4515.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___422_4515.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___422_4515.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___422_4515.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___422_4515.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___422_4515.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___422_4515.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___422_4515.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___422_4515.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___422_4515.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___422_4515.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___422_4515.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___422_4515.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___422_4515.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___422_4515.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___422_4515.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___422_4515.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___422_4515.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___422_4515.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___422_4515.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___422_4515.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4514
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4507 with
                                 | (act_defn,uu____4518,g_d) ->
                                     ((let uu____4521 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4521
                                       then
                                         let uu____4526 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4528 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4526 uu____4528
                                       else ());
                                      (let uu____4533 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4541 =
                                           let uu____4542 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4542.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4541 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4552) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4575 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4575 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4591 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4591 with
                                                   | (a_tm,uu____4611,g_tm)
                                                       ->
                                                       let uu____4625 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4625 with
                                                        | (repr1,g) ->
                                                            let uu____4638 =
                                                              let uu____4641
                                                                =
                                                                let uu____4644
                                                                  =
                                                                  let uu____4647
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4647
                                                                    (
                                                                    fun _4650
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4650)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4644
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4641
                                                               in
                                                            let uu____4651 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4638,
                                                              uu____4651))))
                                         | uu____4654 ->
                                             let uu____4655 =
                                               let uu____4661 =
                                                 let uu____4663 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4663
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4661)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4655 r
                                          in
                                       match uu____4533 with
                                       | (k,g_k) ->
                                           ((let uu____4680 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4680
                                             then
                                               let uu____4685 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4685
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4693 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4693
                                              then
                                                let uu____4698 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4698
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4711 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4711
                                                   in
                                                let repr_args t =
                                                  let uu____4732 =
                                                    let uu____4733 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4733.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4732 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4785 =
                                                        let uu____4786 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4786.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4785 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4795,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4805 ->
                                                           let uu____4806 =
                                                             let uu____4812 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4812)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4806 r)
                                                  | uu____4821 ->
                                                      let uu____4822 =
                                                        let uu____4828 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4828)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4822 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4838 =
                                                  let uu____4839 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4839.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4838 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4864 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4864 with
                                                     | (bs1,c1) ->
                                                         let uu____4871 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4871
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
                                                              let uu____4882
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4882))
                                                | uu____4885 ->
                                                    let uu____4886 =
                                                      let uu____4892 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4892)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4886 r
                                                 in
                                              (let uu____4896 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4896
                                               then
                                                 let uu____4901 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4901
                                               else ());
                                              (let act2 =
                                                 let uu____4907 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4907 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___495_4921 =
                                                         act1  in
                                                       let uu____4922 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___495_4921.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___495_4921.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___495_4921.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4922
                                                       }
                                                     else
                                                       (let uu____4925 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4932
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4932
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4925
                                                        then
                                                          let uu___500_4937 =
                                                            act1  in
                                                          let uu____4938 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___500_4937.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___500_4937.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___500_4937.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___500_4937.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4938
                                                          }
                                                        else
                                                          (let uu____4941 =
                                                             let uu____4947 =
                                                               let uu____4949
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4951
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4949
                                                                 uu____4951
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4947)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4941 r))
                                                  in
                                               act2)))))))))
                       in
                    let fst1 uu____4974 =
                      match uu____4974 with | (a,uu____4990,uu____4991) -> a
                       in
                    let snd1 uu____5023 =
                      match uu____5023 with | (uu____5038,b,uu____5040) -> b
                       in
                    let thd uu____5072 =
                      match uu____5072 with | (uu____5087,uu____5088,c) -> c
                       in
                    let uu___518_5102 = ed  in
                    let uu____5103 =
                      FStar_All.pipe_right
                        ((fst1 stronger_repr), (snd1 stronger_repr))
                        (fun _5112  -> FStar_Pervasives_Native.Some _5112)
                       in
                    let uu____5113 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.is_layered =
                        (true,
                          (FStar_Pervasives_Native.Some underlying_effect_lid));
                      FStar_Syntax_Syntax.cattributes =
                        (uu___518_5102.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___518_5102.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___518_5102.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___518_5102.FStar_Syntax_Syntax.binders);
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
                        (uu___518_5102.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                      FStar_Syntax_Syntax.return_repr =
                        ((fst1 return_repr), (snd1 return_repr));
                      FStar_Syntax_Syntax.bind_repr =
                        ((fst1 bind_repr), (snd1 bind_repr));
                      FStar_Syntax_Syntax.stronger_repr = uu____5103;
                      FStar_Syntax_Syntax.actions = uu____5113;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___518_5102.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5168 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____5168 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5195 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5195
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5217 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5217
         then
           let uu____5222 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5222
         else ());
        (let uu____5228 =
           let uu____5233 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5233 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5257 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5257  in
               let uu____5258 =
                 let uu____5265 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5265 bs  in
               (match uu____5258 with
                | (bs1,uu____5271,uu____5272) ->
                    let uu____5273 =
                      let tmp_t =
                        let uu____5283 =
                          let uu____5286 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5291  ->
                                 FStar_Pervasives_Native.Some _5291)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5286
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5283  in
                      let uu____5292 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5292 with
                      | (us,tmp_t1) ->
                          let uu____5309 =
                            let uu____5310 =
                              let uu____5311 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5311
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5310
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5309)
                       in
                    (match uu____5273 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5380 ->
                              let uu____5383 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5390 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5390 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5383
                              then (us, bs2)
                              else
                                (let uu____5401 =
                                   let uu____5407 =
                                     let uu____5409 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5411 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5409 uu____5411
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5407)
                                    in
                                 let uu____5415 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5401
                                   uu____5415))))
            in
         match uu____5228 with
         | (us,bs) ->
             let ed1 =
               let uu___559_5423 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___559_5423.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___559_5423.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___559_5423.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___559_5423.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___559_5423.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___559_5423.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___559_5423.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___559_5423.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___559_5423.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___559_5423.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___559_5423.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___559_5423.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___559_5423.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___559_5423.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___559_5423.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5424 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5424 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5443 =
                    let uu____5448 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5448  in
                  (match uu____5443 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5469 =
                           match uu____5469 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5489 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5489 t  in
                               let uu____5498 =
                                 let uu____5499 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5499 t1  in
                               (us1, uu____5498)
                            in
                         let uu___573_5504 = ed1  in
                         let uu____5505 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5506 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____5507 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____5508 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____5509 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____5514 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____5517 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____5518 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____5519 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____5520 =
                           FStar_List.map
                             (fun a  ->
                                let uu___576_5528 = a  in
                                let uu____5529 =
                                  let uu____5530 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5530  in
                                let uu____5541 =
                                  let uu____5542 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5542  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___576_5528.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___576_5528.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___576_5528.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___576_5528.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5529;
                                  FStar_Syntax_Syntax.action_typ = uu____5541
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___573_5504.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___573_5504.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___573_5504.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___573_5504.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___573_5504.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5505;
                           FStar_Syntax_Syntax.ret_wp = uu____5506;
                           FStar_Syntax_Syntax.bind_wp = uu____5507;
                           FStar_Syntax_Syntax.stronger = uu____5508;
                           FStar_Syntax_Syntax.match_wps = uu____5509;
                           FStar_Syntax_Syntax.trivial = uu____5514;
                           FStar_Syntax_Syntax.repr = uu____5517;
                           FStar_Syntax_Syntax.return_repr = uu____5518;
                           FStar_Syntax_Syntax.bind_repr = uu____5519;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____5520;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___573_5504.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5554 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5554
                         then
                           let uu____5559 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5559
                         else ());
                        (let env =
                           let uu____5566 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5566
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5601 k =
                           match uu____5601 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5621 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5621 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5630 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          tc_check_trivial_guard uu____5630
                                            t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5631 =
                                            let uu____5638 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5638 t1
                                             in
                                          (match uu____5631 with
                                           | (t2,uu____5640,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5643 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5643 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5659 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5661 =
                                                 let uu____5663 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5663
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5659 uu____5661
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5678 ->
                                               let uu____5679 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5686 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5686 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5679
                                               then (g_us, t3)
                                               else
                                                 (let uu____5697 =
                                                    let uu____5703 =
                                                      let uu____5705 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5707 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5705
                                                        uu____5707
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5703)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5697
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5715 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5715
                          then
                            let uu____5720 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5720
                          else ());
                         (let fresh_a_and_wp uu____5736 =
                            let fail1 t =
                              let uu____5749 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5749
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5765 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5765 with
                            | (uu____5776,signature1) ->
                                let uu____5778 =
                                  let uu____5779 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5779.FStar_Syntax_Syntax.n  in
                                (match uu____5778 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5789) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5818)::(wp,uu____5820)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5849 -> fail1 signature1)
                                 | uu____5850 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5864 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5864
                            then
                              let uu____5869 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5869
                            else ()  in
                          let ret_wp =
                            let uu____5875 = fresh_a_and_wp ()  in
                            match uu____5875 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5891 =
                                    let uu____5900 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5907 =
                                      let uu____5916 =
                                        let uu____5923 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5923
                                         in
                                      [uu____5916]  in
                                    uu____5900 :: uu____5907  in
                                  let uu____5942 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5891
                                    uu____5942
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5950 = fresh_a_and_wp ()  in
                             match uu____5950 with
                             | (a,wp_sort_a) ->
                                 let uu____5963 = fresh_a_and_wp ()  in
                                 (match uu____5963 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5979 =
                                          let uu____5988 =
                                            let uu____5995 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5995
                                             in
                                          [uu____5988]  in
                                        let uu____6008 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5979
                                          uu____6008
                                         in
                                      let k =
                                        let uu____6014 =
                                          let uu____6023 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6030 =
                                            let uu____6039 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6046 =
                                              let uu____6055 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6062 =
                                                let uu____6071 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6078 =
                                                  let uu____6087 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6087]  in
                                                uu____6071 :: uu____6078  in
                                              uu____6055 :: uu____6062  in
                                            uu____6039 :: uu____6046  in
                                          uu____6023 :: uu____6030  in
                                        let uu____6130 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6014
                                          uu____6130
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6138 = fresh_a_and_wp ()  in
                              match uu____6138 with
                              | (a,wp_sort_a) ->
                                  let uu____6151 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6151 with
                                   | (t,uu____6157) ->
                                       let k =
                                         let uu____6161 =
                                           let uu____6170 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6177 =
                                             let uu____6186 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6193 =
                                               let uu____6202 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6202]  in
                                             uu____6186 :: uu____6193  in
                                           uu____6170 :: uu____6177  in
                                         let uu____6233 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6161
                                           uu____6233
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____6245 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____6245 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____6260 = fresh_a_and_wp ()  in
                                     match uu____6260 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____6274 =
                                             let uu____6277 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____6277
                                              in
                                           let uu____6278 =
                                             let uu____6279 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____6279
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____6274 uu____6278
                                            in
                                         let k =
                                           let uu____6291 =
                                             let uu____6300 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____6307 =
                                               let uu____6316 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____6323 =
                                                 let uu____6332 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____6339 =
                                                   let uu____6348 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____6348]  in
                                                 uu____6332 :: uu____6339  in
                                               uu____6316 :: uu____6323  in
                                             uu____6300 :: uu____6307  in
                                           let uu____6385 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____6291
                                             uu____6385
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
                                       let uu____6393 = fresh_a_and_wp ()  in
                                       match uu____6393 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____6409 =
                                               let uu____6418 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6425 =
                                                 let uu____6434 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6434]  in
                                               uu____6418 :: uu____6425  in
                                             let uu____6459 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6409 uu____6459
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____6467 = fresh_a_and_wp ()
                                           in
                                        match uu____6467 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____6481 =
                                                let uu____6484 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____6484
                                                 in
                                              let uu____6485 =
                                                let uu____6486 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____6486
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____6481 uu____6485
                                               in
                                            let wp_sort_b_a =
                                              let uu____6498 =
                                                let uu____6507 =
                                                  let uu____6514 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____6514
                                                   in
                                                [uu____6507]  in
                                              let uu____6527 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6498 uu____6527
                                               in
                                            let k =
                                              let uu____6533 =
                                                let uu____6542 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____6549 =
                                                  let uu____6558 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____6565 =
                                                    let uu____6574 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____6574]  in
                                                  uu____6558 :: uu____6565
                                                   in
                                                uu____6542 :: uu____6549  in
                                              let uu____6605 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____6533 uu____6605
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
                               let uu____6615 = fresh_a_and_wp ()  in
                               match uu____6615 with
                               | (a,wp_sort_a) ->
                                   let uu____6630 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____6630 with
                                    | (t,uu____6638) ->
                                        let k =
                                          let uu____6642 =
                                            let uu____6651 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6658 =
                                              let uu____6667 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____6667]  in
                                            uu____6651 :: uu____6658  in
                                          let uu____6692 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____6642
                                            uu____6692
                                           in
                                        let trivial =
                                          let uu____6696 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____6696
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____6711 =
                               let uu____6722 =
                                 let uu____6723 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____6723.FStar_Syntax_Syntax.n  in
                               match uu____6722 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____6742 ->
                                   let repr =
                                     let uu____6744 = fresh_a_and_wp ()  in
                                     match uu____6744 with
                                     | (a,wp_sort_a) ->
                                         let uu____6757 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____6757 with
                                          | (t,uu____6763) ->
                                              let k =
                                                let uu____6767 =
                                                  let uu____6776 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____6783 =
                                                    let uu____6792 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____6792]  in
                                                  uu____6776 :: uu____6783
                                                   in
                                                let uu____6817 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____6767 uu____6817
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
                                       let uu____6837 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____6837 with
                                       | (uu____6844,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____6847 =
                                             let uu____6854 =
                                               let uu____6855 =
                                                 let uu____6872 =
                                                   let uu____6883 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6900 =
                                                     let uu____6911 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6911]  in
                                                   uu____6883 :: uu____6900
                                                    in
                                                 (repr2, uu____6872)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____6855
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____6854
                                              in
                                           uu____6847
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____6977 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____6977 wp  in
                                     let destruct_repr t =
                                       let uu____6992 =
                                         let uu____6993 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____6993.FStar_Syntax_Syntax.n  in
                                       match uu____6992 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____7004,(t1,uu____7006)::
                                            (wp,uu____7008)::[])
                                           -> (t1, wp)
                                       | uu____7067 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____7078 = fresh_a_and_wp ()  in
                                       match uu____7078 with
                                       | (a,uu____7086) ->
                                           let x_a =
                                             let uu____7092 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____7092
                                              in
                                           let res =
                                             let wp =
                                               let uu____7100 =
                                                 let uu____7105 =
                                                   let uu____7106 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7106
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____7115 =
                                                   let uu____7116 =
                                                     let uu____7125 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____7125
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____7134 =
                                                     let uu____7145 =
                                                       let uu____7154 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____7154
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____7145]  in
                                                   uu____7116 :: uu____7134
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____7105 uu____7115
                                                  in
                                               uu____7100
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____7190 =
                                               let uu____7199 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____7206 =
                                                 let uu____7215 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____7215]  in
                                               uu____7199 :: uu____7206  in
                                             let uu____7240 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____7190 uu____7240
                                              in
                                           let uu____7243 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____7243 with
                                            | (k1,uu____7251,uu____7252) ->
                                                let env1 =
                                                  let uu____7256 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____7256
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
                                          let uu____7267 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____7267
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____7268 = fresh_a_and_wp ()
                                           in
                                        match uu____7268 with
                                        | (a,wp_sort_a) ->
                                            let uu____7281 =
                                              fresh_a_and_wp ()  in
                                            (match uu____7281 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____7297 =
                                                     let uu____7306 =
                                                       let uu____7313 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____7313
                                                        in
                                                     [uu____7306]  in
                                                   let uu____7326 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7297 uu____7326
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
                                                   let uu____7334 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____7334
                                                    in
                                                 let wp_g_x =
                                                   let uu____7339 =
                                                     let uu____7344 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____7345 =
                                                       let uu____7346 =
                                                         let uu____7355 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7355
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____7346]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____7344 uu____7345
                                                      in
                                                   uu____7339
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____7386 =
                                                       let uu____7391 =
                                                         let uu____7392 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____7392
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____7401 =
                                                         let uu____7402 =
                                                           let uu____7405 =
                                                             let uu____7408 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____7409 =
                                                               let uu____7412
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____7413
                                                                 =
                                                                 let uu____7416
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____7417
                                                                   =
                                                                   let uu____7420
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____7420]
                                                                    in
                                                                 uu____7416
                                                                   ::
                                                                   uu____7417
                                                                  in
                                                               uu____7412 ::
                                                                 uu____7413
                                                                in
                                                             uu____7408 ::
                                                               uu____7409
                                                              in
                                                           r :: uu____7405
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____7402
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____7391
                                                         uu____7401
                                                        in
                                                     uu____7386
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____7438 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____7438
                                                   then
                                                     let uu____7449 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____7456 =
                                                       let uu____7465 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____7465]  in
                                                     uu____7449 :: uu____7456
                                                   else []  in
                                                 let k =
                                                   let uu____7501 =
                                                     let uu____7510 =
                                                       let uu____7519 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____7526 =
                                                         let uu____7535 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____7535]  in
                                                       uu____7519 ::
                                                         uu____7526
                                                        in
                                                     let uu____7560 =
                                                       let uu____7569 =
                                                         let uu____7578 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____7585 =
                                                           let uu____7594 =
                                                             let uu____7601 =
                                                               let uu____7602
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____7602
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____7601
                                                              in
                                                           let uu____7603 =
                                                             let uu____7612 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____7619 =
                                                               let uu____7628
                                                                 =
                                                                 let uu____7635
                                                                   =
                                                                   let uu____7636
                                                                    =
                                                                    let uu____7645
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7645]
                                                                     in
                                                                   let uu____7664
                                                                    =
                                                                    let uu____7667
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7667
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____7636
                                                                    uu____7664
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____7635
                                                                  in
                                                               [uu____7628]
                                                                in
                                                             uu____7612 ::
                                                               uu____7619
                                                              in
                                                           uu____7594 ::
                                                             uu____7603
                                                            in
                                                         uu____7578 ::
                                                           uu____7585
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____7569
                                                        in
                                                     FStar_List.append
                                                       uu____7510 uu____7560
                                                      in
                                                   let uu____7712 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7501 uu____7712
                                                    in
                                                 let uu____7715 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____7715 with
                                                  | (k1,uu____7723,uu____7724)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___774_7736
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___774_7736.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _7738  ->
                                                             FStar_Pervasives_Native.Some
                                                               _7738)
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
                                           (let uu____7765 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____7779 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____7779 with
                                                 | (usubst,uvs) ->
                                                     let uu____7802 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____7803 =
                                                       let uu___787_7804 =
                                                         act  in
                                                       let uu____7805 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____7806 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___787_7804.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___787_7804.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___787_7804.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____7805;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7806
                                                       }  in
                                                     (uu____7802, uu____7803))
                                               in
                                            match uu____7765 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____7810 =
                                                    let uu____7811 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____7811.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____7810 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____7837 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____7837
                                                      then
                                                        let uu____7840 =
                                                          let uu____7843 =
                                                            let uu____7844 =
                                                              let uu____7845
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____7845
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____7844
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____7843
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____7840
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____7868 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____7869 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____7869 with
                                                 | (act_typ1,uu____7877,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___804_7880 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___804_7880.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____7883 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____7883
                                                       then
                                                         let uu____7887 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____7889 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____7891 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____7887
                                                           uu____7889
                                                           uu____7891
                                                       else ());
                                                      (let uu____7896 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____7896 with
                                                       | (act_defn,uu____7904,g_a)
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
                                                           let uu____7908 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____7944
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____7944
                                                                  with
                                                                  | (bs2,uu____7956)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____7963
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7963
                                                                     in
                                                                    let uu____7966
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____7966
                                                                    with
                                                                    | 
                                                                    (k1,uu____7980,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____7984 ->
                                                                 let uu____7985
                                                                   =
                                                                   let uu____7991
                                                                    =
                                                                    let uu____7993
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7995
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7993
                                                                    uu____7995
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7991)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____7985
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____7908
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____8013
                                                                    =
                                                                    let uu____8014
                                                                    =
                                                                    let uu____8015
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8015
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8014
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8013);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____8017
                                                                    =
                                                                    let uu____8018
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8018.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8017
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8043
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8043
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8050
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8050
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8070
                                                                    =
                                                                    let uu____8071
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8071]
                                                                     in
                                                                    let uu____8072
                                                                    =
                                                                    let uu____8083
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8083]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8070;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8072;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8108
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8108))
                                                                    | 
                                                                    uu____8111
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____8113
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8135
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8135))
                                                                     in
                                                                  match uu____8113
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
                                                                    let uu___854_8154
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___854_8154.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___854_8154.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___854_8154.FStar_Syntax_Syntax.action_params);
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
                             match uu____6711 with
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
                                   let uu____8179 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____8179 ts1
                                    in
                                 let ed3 =
                                   let uu___866_8189 = ed2  in
                                   let uu____8190 = cl signature  in
                                   let uu____8191 = cl ret_wp  in
                                   let uu____8192 = cl bind_wp  in
                                   let uu____8193 = cl stronger  in
                                   let uu____8194 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____8199 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____8202 = cl repr  in
                                   let uu____8203 = cl return_repr  in
                                   let uu____8204 = cl bind_repr  in
                                   let uu____8205 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___869_8213 = a  in
                                          let uu____8214 =
                                            let uu____8215 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____8215
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____8240 =
                                            let uu____8241 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____8241
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___869_8213.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___869_8213.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___869_8213.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___869_8213.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____8214;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____8240
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___866_8189.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___866_8189.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___866_8189.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___866_8189.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___866_8189.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____8190;
                                     FStar_Syntax_Syntax.ret_wp = uu____8191;
                                     FStar_Syntax_Syntax.bind_wp = uu____8192;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____8193;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____8194;
                                     FStar_Syntax_Syntax.trivial = uu____8199;
                                     FStar_Syntax_Syntax.repr = uu____8202;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____8203;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____8204;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____8205;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___866_8189.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____8267 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____8267
                                   then
                                     let uu____8272 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____8272
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
        let fail1 uu____8337 =
          let uu____8338 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8344 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8338 uu____8344  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8388)::(wp,uu____8390)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8419 -> fail1 ())
        | uu____8420 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8433 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8433
       then
         let uu____8438 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8438
       else ());
      (let uu____8443 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8443 with
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
             let uu____8476 =
               ((FStar_Pervasives_Native.fst
                   src_ed.FStar_Syntax_Syntax.is_layered)
                  &&
                  (let uu____8482 =
                     let uu____8483 =
                       FStar_All.pipe_right
                         src_ed.FStar_Syntax_Syntax.is_layered
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____8483 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8482
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_Pervasives_Native.fst
                      tgt_ed.FStar_Syntax_Syntax.is_layered)
                     &&
                     (let uu____8504 =
                        let uu____8505 =
                          FStar_All.pipe_right
                            tgt_ed.FStar_Syntax_Syntax.is_layered
                            FStar_Pervasives_Native.snd
                           in
                        FStar_All.pipe_right uu____8505 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8504
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8523 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8523))
                in
             if uu____8476
             then
               let uu____8526 =
                 let uu____8532 =
                   let uu____8534 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8537 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8534 uu____8537
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8532)  in
               FStar_Errors.raise_error uu____8526 r
             else ());
            (let uu____8544 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8568 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8568 with
                  | (us1,lift1) ->
                      let uu____8583 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8583, us1, lift1))
                in
             match uu____8544 with
             | (env,us1,lift1) ->
                 let uu____8593 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8593 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8606 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8606
                         then
                           let uu____8611 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8613 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8611 uu____8613
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8627 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8629 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8631 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8627 uu____8629 s uu____8631
                            in
                         let uu____8634 =
                           let uu____8641 =
                             let uu____8646 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8646
                               (fun uu____8663  ->
                                  match uu____8663 with
                                  | (t,u) ->
                                      let uu____8674 =
                                        let uu____8675 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8675
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8674, u))
                              in
                           match uu____8641 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8694 =
                                   let uu____8695 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8695.FStar_Syntax_Syntax.n  in
                                 match uu____8694 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8707) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8735 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8735 with
                                      | (a',uu____8745)::bs1 ->
                                          let uu____8765 =
                                            let uu____8766 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8766
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8864 =
                                            let uu____8877 =
                                              let uu____8880 =
                                                let uu____8881 =
                                                  let uu____8888 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8888)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8881
                                                 in
                                              [uu____8880]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8877
                                             in
                                          FStar_All.pipe_right uu____8765
                                            uu____8864)
                                 | uu____8903 ->
                                     let uu____8904 =
                                       let uu____8910 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____8910)
                                        in
                                     FStar_Errors.raise_error uu____8904 r
                                  in
                               let uu____8922 =
                                 let uu____8933 =
                                   let uu____8938 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____8945 =
                                     let uu____8946 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____8946
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____8938 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____8945
                                    in
                                 match uu____8933 with
                                 | (f_sort,g1) ->
                                     let uu____8967 =
                                       let uu____8974 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____8974
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____8967, g1)
                                  in
                               (match uu____8922 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9041 =
                                      let uu____9046 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9047 =
                                        let uu____9048 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9048
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9046 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9047
                                       in
                                    (match uu____9041 with
                                     | (repr,g_repr) ->
                                         let uu____9065 =
                                           let uu____9068 =
                                             let uu____9071 =
                                               let uu____9074 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9074
                                                 (fun _9077  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9077)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9071
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9068
                                            in
                                         let uu____9078 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9065, uu____9078)))
                            in
                         match uu____8634 with
                         | (k,g_k) ->
                             ((let uu____9088 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9088
                               then
                                 let uu____9093 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9093
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9102 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9102
                                then
                                  let uu____9107 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9107
                                else ());
                               (let uu____9112 =
                                  let uu____9125 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9125 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9152 =
                                            let uu____9158 =
                                              let uu____9160 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9162 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9164 =
                                                let uu____9166 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9166
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9173 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9160 uu____9162
                                                uu____9164 uu____9173
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9158)
                                             in
                                          FStar_Errors.raise_error uu____9152
                                            r)
                                       else ();
                                       (let uu____9179 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9188 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9188 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9179
                                        then
                                          let uu____9205 =
                                            let uu____9208 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9208
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9205)
                                        else
                                          (let uu____9219 =
                                             let uu____9225 =
                                               let uu____9227 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9229 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9231 =
                                                 let uu____9233 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9233
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9240 =
                                                 let uu____9242 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9242
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9249 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9227 uu____9229
                                                 uu____9231 uu____9240
                                                 uu____9249
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9225)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9219 r)))
                                   in
                                match uu____9112 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___977_9281 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___977_9281.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___977_9281.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9291 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9291
                                      then
                                        let uu____9296 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9296
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
          (let uu____9328 =
             let uu____9335 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9335
              in
           match uu____9328 with
           | (a,wp_a_src) ->
               let uu____9342 =
                 let uu____9349 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9349
                  in
               (match uu____9342 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9357 =
                        let uu____9360 =
                          let uu____9361 =
                            let uu____9368 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9368)  in
                          FStar_Syntax_Syntax.NT uu____9361  in
                        [uu____9360]  in
                      FStar_Syntax_Subst.subst uu____9357 wp_b_tgt  in
                    let expected_k =
                      let uu____9376 =
                        let uu____9385 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9392 =
                          let uu____9401 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9401]  in
                        uu____9385 :: uu____9392  in
                      let uu____9426 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9376 uu____9426  in
                    let repr_type eff_name a1 wp =
                      (let uu____9448 =
                         let uu____9450 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9450  in
                       if uu____9448
                       then
                         let uu____9453 =
                           let uu____9459 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9459)
                            in
                         let uu____9463 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9453 uu____9463
                       else ());
                      (let uu____9466 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9466 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____9499 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9500 =
                             let uu____9507 =
                               let uu____9508 =
                                 let uu____9525 =
                                   let uu____9536 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9545 =
                                     let uu____9556 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9556]  in
                                   uu____9536 :: uu____9545  in
                                 (repr, uu____9525)  in
                               FStar_Syntax_Syntax.Tm_app uu____9508  in
                             FStar_Syntax_Syntax.mk uu____9507  in
                           uu____9500 FStar_Pervasives_Native.None uu____9499)
                       in
                    let uu____9601 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9774 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9785 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9785 with
                              | (usubst,uvs1) ->
                                  let uu____9808 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9809 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9808, uu____9809)
                            else (env, lift_wp)  in
                          (match uu____9774 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____9859 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9859))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9930 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9945 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9945 with
                              | (usubst,uvs) ->
                                  let uu____9970 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9970)
                            else ([], lift)  in
                          (match uu____9930 with
                           | (uvs,lift1) ->
                               ((let uu____10006 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10006
                                 then
                                   let uu____10010 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10010
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10016 =
                                   let uu____10023 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10023 lift1
                                    in
                                 match uu____10016 with
                                 | (lift2,comp,uu____10048) ->
                                     let uu____10049 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10049 with
                                      | (uu____10078,lift_wp,lift_elab) ->
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
                                            let uu____10110 =
                                              let uu____10121 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10121
                                               in
                                            let uu____10138 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10110, uu____10138)
                                          else
                                            (let uu____10167 =
                                               let uu____10178 =
                                                 let uu____10187 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10187)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10178
                                                in
                                             let uu____10202 =
                                               let uu____10211 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10211)  in
                                             (uu____10167, uu____10202))))))
                       in
                    (match uu____9601 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1057_10275 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1057_10275.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1057_10275.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1057_10275.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1057_10275.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1057_10275.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1057_10275.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1057_10275.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1057_10275.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1057_10275.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1057_10275.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1057_10275.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1057_10275.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1057_10275.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1057_10275.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1057_10275.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1057_10275.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1057_10275.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1057_10275.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1057_10275.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1057_10275.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1057_10275.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1057_10275.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1057_10275.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1057_10275.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1057_10275.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1057_10275.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1057_10275.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1057_10275.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1057_10275.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1057_10275.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1057_10275.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1057_10275.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1057_10275.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1057_10275.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1057_10275.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1057_10275.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1057_10275.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1057_10275.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1057_10275.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1057_10275.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1057_10275.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1057_10275.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1057_10275.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1057_10275.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10308 =
                                 let uu____10313 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10313 with
                                 | (usubst,uvs1) ->
                                     let uu____10336 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10337 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10336, uu____10337)
                                  in
                               (match uu____10308 with
                                | (env2,lift2) ->
                                    let uu____10342 =
                                      let uu____10349 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10349
                                       in
                                    (match uu____10342 with
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
                                             let uu____10375 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10376 =
                                               let uu____10383 =
                                                 let uu____10384 =
                                                   let uu____10401 =
                                                     let uu____10412 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10421 =
                                                       let uu____10432 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10432]  in
                                                     uu____10412 ::
                                                       uu____10421
                                                      in
                                                   (lift_wp1, uu____10401)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10384
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10383
                                                in
                                             uu____10376
                                               FStar_Pervasives_Native.None
                                               uu____10375
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10480 =
                                             let uu____10489 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10496 =
                                               let uu____10505 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10512 =
                                                 let uu____10521 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10521]  in
                                               uu____10505 :: uu____10512  in
                                             uu____10489 :: uu____10496  in
                                           let uu____10552 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10480 uu____10552
                                            in
                                         let uu____10555 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10555 with
                                          | (expected_k2,uu____10565,uu____10566)
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
                                                   let uu____10574 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10574))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10582 =
                             let uu____10584 =
                               let uu____10586 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10586
                                 FStar_List.length
                                in
                             uu____10584 <> Prims.int_one  in
                           if uu____10582
                           then
                             let uu____10609 =
                               let uu____10615 =
                                 let uu____10617 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10619 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10621 =
                                   let uu____10623 =
                                     let uu____10625 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10625
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10623
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10617 uu____10619 uu____10621
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10615)
                                in
                             FStar_Errors.raise_error uu____10609 r
                           else ());
                          (let uu____10652 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10655 =
                                  let uu____10657 =
                                    let uu____10660 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10660
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10657
                                    FStar_List.length
                                   in
                                uu____10655 <> Prims.int_one)
                              in
                           if uu____10652
                           then
                             let uu____10698 =
                               let uu____10704 =
                                 let uu____10706 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10708 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10710 =
                                   let uu____10712 =
                                     let uu____10714 =
                                       let uu____10717 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10717
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10714
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10712
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10706 uu____10708 uu____10710
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10704)
                                in
                             FStar_Errors.raise_error uu____10698 r
                           else ());
                          (let uu___1094_10759 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1094_10759.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1094_10759.FStar_Syntax_Syntax.target);
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
    fun uu____10790  ->
      fun r  ->
        match uu____10790 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10813 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10841 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10841 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10872 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10872 c  in
                     let uu____10881 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10881, uvs1, tps1, c1))
               in
            (match uu____10813 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10901 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10901 with
                  | (tps2,c2) ->
                      let uu____10916 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10916 with
                       | (tps3,env3,us) ->
                           let uu____10934 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10934 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10960)::uu____10961 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10980 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10988 =
                                    let uu____10990 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10990  in
                                  if uu____10988
                                  then
                                    let uu____10993 =
                                      let uu____10999 =
                                        let uu____11001 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11003 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11001 uu____11003
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10999)
                                       in
                                    FStar_Errors.raise_error uu____10993 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11011 =
                                    let uu____11012 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11012
                                     in
                                  match uu____11011 with
                                  | (uvs2,t) ->
                                      let uu____11041 =
                                        let uu____11046 =
                                          let uu____11059 =
                                            let uu____11060 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11060.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11059)  in
                                        match uu____11046 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11075,c5)) -> ([], c5)
                                        | (uu____11117,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11156 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11041 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11188 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11188 with
                                               | (uu____11193,t1) ->
                                                   let uu____11195 =
                                                     let uu____11201 =
                                                       let uu____11203 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11205 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11209 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11203
                                                         uu____11205
                                                         uu____11209
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11201)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11195 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  