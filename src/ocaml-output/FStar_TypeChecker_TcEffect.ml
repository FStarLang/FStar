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
                                                     uu____2925 uu____2992)
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
                        (let uu____3366 =
                           let uu____3372 =
                             let uu____3374 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____3374
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____3372)
                            in
                         FStar_Errors.raise_error uu____3366 r)
                      else ();
                      (let uu____3381 =
                         let uu____3386 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____3386 with
                         | (usubst,us) ->
                             let uu____3409 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____3410 =
                               let uu___336_3411 = act  in
                               let uu____3412 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____3413 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___336_3411.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___336_3411.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___336_3411.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____3412;
                                 FStar_Syntax_Syntax.action_typ = uu____3413
                               }  in
                             (uu____3409, uu____3410)
                          in
                       match uu____3381 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____3417 =
                               let uu____3418 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____3418.FStar_Syntax_Syntax.n  in
                             match uu____3417 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____3444 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____3444
                                 then
                                   let repr_ts =
                                     let uu____3448 = repr  in
                                     match uu____3448 with
                                     | (us,t,uu____3463) -> (us, t)  in
                                   let repr1 =
                                     let uu____3481 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____3481
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____3493 =
                                       let uu____3498 =
                                         let uu____3499 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____3499 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____3498
                                        in
                                     uu____3493 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____3517 =
                                       let uu____3520 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____3520
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____3517
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____3523 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____3524 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____3524 with
                            | (act_typ1,uu____3532,g_t) ->
                                let uu____3534 =
                                  let uu____3541 =
                                    let uu___361_3542 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___361_3542.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___361_3542.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___361_3542.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___361_3542.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___361_3542.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___361_3542.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___361_3542.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___361_3542.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___361_3542.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___361_3542.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___361_3542.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___361_3542.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___361_3542.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___361_3542.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___361_3542.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___361_3542.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___361_3542.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___361_3542.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___361_3542.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___361_3542.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___361_3542.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___361_3542.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___361_3542.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___361_3542.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___361_3542.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___361_3542.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___361_3542.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___361_3542.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___361_3542.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___361_3542.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___361_3542.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___361_3542.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___361_3542.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___361_3542.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___361_3542.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___361_3542.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___361_3542.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___361_3542.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___361_3542.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___361_3542.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___361_3542.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___361_3542.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___361_3542.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___361_3542.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____3541
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____3534 with
                                 | (act_defn,uu____3545,g_d) ->
                                     ((let uu____3548 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3548
                                       then
                                         let uu____3553 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____3555 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____3553 uu____3555
                                       else ());
                                      (let uu____3560 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____3568 =
                                           let uu____3569 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____3569.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3568 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____3579) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____3602 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____3602 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____3618 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____3618 with
                                                   | (a_tm,uu____3638,g_tm)
                                                       ->
                                                       let uu____3652 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____3652 with
                                                        | (repr1,g) ->
                                                            let uu____3665 =
                                                              let uu____3668
                                                                =
                                                                let uu____3671
                                                                  =
                                                                  let uu____3674
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____3674
                                                                    (
                                                                    fun _3677
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _3677)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____3671
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____3668
                                                               in
                                                            let uu____3678 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____3665,
                                                              uu____3678))))
                                         | uu____3681 ->
                                             let uu____3682 =
                                               let uu____3688 =
                                                 let uu____3690 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____3690
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____3688)
                                                in
                                             FStar_Errors.raise_error
                                               uu____3682 r
                                          in
                                       match uu____3560 with
                                       | (k,g_k) ->
                                           ((let uu____3707 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____3707
                                             then
                                               let uu____3712 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____3712
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____3720 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____3720
                                              then
                                                let uu____3725 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____3725
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____3738 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____3738
                                                   in
                                                let repr_args t =
                                                  let uu____3759 =
                                                    let uu____3760 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____3760.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____3759 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____3812 =
                                                        let uu____3813 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____3813.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3812 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____3822,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____3832 ->
                                                           let uu____3833 =
                                                             let uu____3839 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____3839)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3833 r)
                                                  | uu____3848 ->
                                                      let uu____3849 =
                                                        let uu____3855 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____3855)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____3849 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____3865 =
                                                  let uu____3866 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____3866.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____3865 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____3891 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____3891 with
                                                     | (bs1,c1) ->
                                                         let uu____3898 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____3898
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
                                                              let uu____3909
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____3909))
                                                | uu____3912 ->
                                                    let uu____3913 =
                                                      let uu____3919 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____3919)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3913 r
                                                 in
                                              (let uu____3923 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3923
                                               then
                                                 let uu____3928 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____3928
                                               else ());
                                              (let act2 =
                                                 let uu____3934 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____3934 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___434_3948 =
                                                         act1  in
                                                       let uu____3949 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___434_3948.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___434_3948.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___434_3948.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____3949
                                                       }
                                                     else
                                                       (let uu____3952 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____3959
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____3959
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____3952
                                                        then
                                                          let uu___439_3964 =
                                                            act1  in
                                                          let uu____3965 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___439_3964.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___439_3964.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___439_3964.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___439_3964.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____3965
                                                          }
                                                        else
                                                          (let uu____3968 =
                                                             let uu____3974 =
                                                               let uu____3976
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____3978
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____3976
                                                                 uu____3978
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____3974)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3968 r))
                                                  in
                                               act2)))))))))
                       in
                    let fst1 uu____4001 =
                      match uu____4001 with | (a,uu____4017,uu____4018) -> a
                       in
                    let snd1 uu____4050 =
                      match uu____4050 with | (uu____4065,b,uu____4067) -> b
                       in
                    let thd uu____4099 =
                      match uu____4099 with | (uu____4114,uu____4115,c) -> c
                       in
                    let uu___457_4129 = ed  in
                    let uu____4130 =
                      FStar_All.pipe_right
                        ((fst1 stronger_repr), (snd1 stronger_repr))
                        (fun _4139  -> FStar_Pervasives_Native.Some _4139)
                       in
                    let uu____4140 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.is_layered =
                        (true,
                          (FStar_Pervasives_Native.Some underlying_effect_lid));
                      FStar_Syntax_Syntax.cattributes =
                        (uu___457_4129.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___457_4129.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___457_4129.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___457_4129.FStar_Syntax_Syntax.binders);
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
                        (uu___457_4129.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                      FStar_Syntax_Syntax.return_repr =
                        ((fst1 return_repr), (snd1 return_repr));
                      FStar_Syntax_Syntax.bind_repr =
                        ((fst1 bind_repr), (snd1 bind_repr));
                      FStar_Syntax_Syntax.stronger_repr = uu____4130;
                      FStar_Syntax_Syntax.actions = uu____4140;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___457_4129.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4195 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____4195 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4222 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____4222
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____4244 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____4244
         then
           let uu____4249 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4249
         else ());
        (let uu____4255 =
           let uu____4260 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____4260 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____4284 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____4284  in
               let uu____4285 =
                 let uu____4292 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____4292 bs  in
               (match uu____4285 with
                | (bs1,uu____4298,uu____4299) ->
                    let uu____4300 =
                      let tmp_t =
                        let uu____4310 =
                          let uu____4313 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _4318  ->
                                 FStar_Pervasives_Native.Some _4318)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____4313
                           in
                        FStar_Syntax_Util.arrow bs1 uu____4310  in
                      let uu____4319 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____4319 with
                      | (us,tmp_t1) ->
                          let uu____4336 =
                            let uu____4337 =
                              let uu____4338 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____4338
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____4337
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____4336)
                       in
                    (match uu____4300 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____4407 ->
                              let uu____4410 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____4417 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____4417 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____4410
                              then (us, bs2)
                              else
                                (let uu____4428 =
                                   let uu____4434 =
                                     let uu____4436 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____4438 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____4436 uu____4438
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____4434)
                                    in
                                 let uu____4442 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____4428
                                   uu____4442))))
            in
         match uu____4255 with
         | (us,bs) ->
             let ed1 =
               let uu___498_4450 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___498_4450.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___498_4450.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___498_4450.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___498_4450.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___498_4450.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___498_4450.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___498_4450.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___498_4450.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___498_4450.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___498_4450.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___498_4450.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___498_4450.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___498_4450.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___498_4450.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___498_4450.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____4451 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____4451 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____4470 =
                    let uu____4475 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____4475  in
                  (match uu____4470 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____4496 =
                           match uu____4496 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____4516 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4516 t  in
                               let uu____4525 =
                                 let uu____4526 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4526 t1  in
                               (us1, uu____4525)
                            in
                         let uu___512_4531 = ed1  in
                         let uu____4532 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____4533 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____4534 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____4535 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____4536 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____4541 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____4544 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____4545 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____4546 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____4547 =
                           FStar_List.map
                             (fun a  ->
                                let uu___515_4555 = a  in
                                let uu____4556 =
                                  let uu____4557 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____4557  in
                                let uu____4568 =
                                  let uu____4569 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____4569  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___515_4555.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___515_4555.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___515_4555.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___515_4555.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____4556;
                                  FStar_Syntax_Syntax.action_typ = uu____4568
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___512_4531.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___512_4531.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___512_4531.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___512_4531.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___512_4531.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____4532;
                           FStar_Syntax_Syntax.ret_wp = uu____4533;
                           FStar_Syntax_Syntax.bind_wp = uu____4534;
                           FStar_Syntax_Syntax.stronger = uu____4535;
                           FStar_Syntax_Syntax.match_wps = uu____4536;
                           FStar_Syntax_Syntax.trivial = uu____4541;
                           FStar_Syntax_Syntax.repr = uu____4544;
                           FStar_Syntax_Syntax.return_repr = uu____4545;
                           FStar_Syntax_Syntax.bind_repr = uu____4546;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____4547;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___512_4531.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____4581 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____4581
                         then
                           let uu____4586 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____4586
                         else ());
                        (let env =
                           let uu____4593 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____4593
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____4628 k =
                           match uu____4628 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____4648 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____4648 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____4657 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          tc_check_trivial_guard uu____4657
                                            t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____4658 =
                                            let uu____4665 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____4665 t1
                                             in
                                          (match uu____4658 with
                                           | (t2,uu____4667,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____4670 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____4670 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____4686 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____4688 =
                                                 let uu____4690 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____4690
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____4686 uu____4688
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____4705 ->
                                               let uu____4706 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____4713 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____4713 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____4706
                                               then (g_us, t3)
                                               else
                                                 (let uu____4724 =
                                                    let uu____4730 =
                                                      let uu____4732 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____4734 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____4732
                                                        uu____4734
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____4730)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____4724
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____4742 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4742
                          then
                            let uu____4747 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____4747
                          else ());
                         (let fresh_a_and_wp uu____4763 =
                            let fail1 t =
                              let uu____4776 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____4776
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____4792 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____4792 with
                            | (uu____4803,signature1) ->
                                let uu____4805 =
                                  let uu____4806 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____4806.FStar_Syntax_Syntax.n  in
                                (match uu____4805 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____4816) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____4845)::(wp,uu____4847)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____4876 -> fail1 signature1)
                                 | uu____4877 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____4891 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____4891
                            then
                              let uu____4896 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____4896
                            else ()  in
                          let ret_wp =
                            let uu____4902 = fresh_a_and_wp ()  in
                            match uu____4902 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____4918 =
                                    let uu____4927 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____4934 =
                                      let uu____4943 =
                                        let uu____4950 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____4950
                                         in
                                      [uu____4943]  in
                                    uu____4927 :: uu____4934  in
                                  let uu____4969 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____4918
                                    uu____4969
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____4977 = fresh_a_and_wp ()  in
                             match uu____4977 with
                             | (a,wp_sort_a) ->
                                 let uu____4990 = fresh_a_and_wp ()  in
                                 (match uu____4990 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5006 =
                                          let uu____5015 =
                                            let uu____5022 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5022
                                             in
                                          [uu____5015]  in
                                        let uu____5035 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5006
                                          uu____5035
                                         in
                                      let k =
                                        let uu____5041 =
                                          let uu____5050 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5057 =
                                            let uu____5066 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5073 =
                                              let uu____5082 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5089 =
                                                let uu____5098 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5105 =
                                                  let uu____5114 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5114]  in
                                                uu____5098 :: uu____5105  in
                                              uu____5082 :: uu____5089  in
                                            uu____5066 :: uu____5073  in
                                          uu____5050 :: uu____5057  in
                                        let uu____5157 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5041
                                          uu____5157
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5165 = fresh_a_and_wp ()  in
                              match uu____5165 with
                              | (a,wp_sort_a) ->
                                  let uu____5178 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____5178 with
                                   | (t,uu____5184) ->
                                       let k =
                                         let uu____5188 =
                                           let uu____5197 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5204 =
                                             let uu____5213 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____5220 =
                                               let uu____5229 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5229]  in
                                             uu____5213 :: uu____5220  in
                                           uu____5197 :: uu____5204  in
                                         let uu____5260 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____5188
                                           uu____5260
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____5272 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____5272 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____5287 = fresh_a_and_wp ()  in
                                     match uu____5287 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____5301 =
                                             let uu____5304 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____5304
                                              in
                                           let uu____5305 =
                                             let uu____5306 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____5306
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____5301 uu____5305
                                            in
                                         let k =
                                           let uu____5318 =
                                             let uu____5327 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5334 =
                                               let uu____5343 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____5350 =
                                                 let uu____5359 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____5366 =
                                                   let uu____5375 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____5375]  in
                                                 uu____5359 :: uu____5366  in
                                               uu____5343 :: uu____5350  in
                                             uu____5327 :: uu____5334  in
                                           let uu____5412 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5318
                                             uu____5412
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
                                       let uu____5420 = fresh_a_and_wp ()  in
                                       match uu____5420 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____5436 =
                                               let uu____5445 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____5452 =
                                                 let uu____5461 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5461]  in
                                               uu____5445 :: uu____5452  in
                                             let uu____5486 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____5436 uu____5486
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____5494 = fresh_a_and_wp ()
                                           in
                                        match uu____5494 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____5508 =
                                                let uu____5511 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5511
                                                 in
                                              let uu____5512 =
                                                let uu____5513 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____5513
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____5508 uu____5512
                                               in
                                            let wp_sort_b_a =
                                              let uu____5525 =
                                                let uu____5534 =
                                                  let uu____5541 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____5541
                                                   in
                                                [uu____5534]  in
                                              let uu____5554 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5525 uu____5554
                                               in
                                            let k =
                                              let uu____5560 =
                                                let uu____5569 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5576 =
                                                  let uu____5585 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____5592 =
                                                    let uu____5601 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____5601]  in
                                                  uu____5585 :: uu____5592
                                                   in
                                                uu____5569 :: uu____5576  in
                                              let uu____5632 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5560 uu____5632
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
                               let uu____5642 = fresh_a_and_wp ()  in
                               match uu____5642 with
                               | (a,wp_sort_a) ->
                                   let uu____5657 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____5657 with
                                    | (t,uu____5665) ->
                                        let k =
                                          let uu____5669 =
                                            let uu____5678 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5685 =
                                              let uu____5694 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____5694]  in
                                            uu____5678 :: uu____5685  in
                                          let uu____5719 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____5669
                                            uu____5719
                                           in
                                        let trivial =
                                          let uu____5723 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____5723
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____5738 =
                               let uu____5749 =
                                 let uu____5750 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____5750.FStar_Syntax_Syntax.n  in
                               match uu____5749 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____5769 ->
                                   let repr =
                                     let uu____5771 = fresh_a_and_wp ()  in
                                     match uu____5771 with
                                     | (a,wp_sort_a) ->
                                         let uu____5784 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____5784 with
                                          | (t,uu____5790) ->
                                              let k =
                                                let uu____5794 =
                                                  let uu____5803 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____5810 =
                                                    let uu____5819 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____5819]  in
                                                  uu____5803 :: uu____5810
                                                   in
                                                let uu____5844 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5794 uu____5844
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
                                       let uu____5864 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____5864 with
                                       | (uu____5871,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____5874 =
                                             let uu____5881 =
                                               let uu____5882 =
                                                 let uu____5899 =
                                                   let uu____5910 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____5927 =
                                                     let uu____5938 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5938]  in
                                                   uu____5910 :: uu____5927
                                                    in
                                                 (repr2, uu____5899)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____5882
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____5881
                                              in
                                           uu____5874
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____6004 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____6004 wp  in
                                     let destruct_repr t =
                                       let uu____6019 =
                                         let uu____6020 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____6020.FStar_Syntax_Syntax.n  in
                                       match uu____6019 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____6031,(t1,uu____6033)::
                                            (wp,uu____6035)::[])
                                           -> (t1, wp)
                                       | uu____6094 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____6105 = fresh_a_and_wp ()  in
                                       match uu____6105 with
                                       | (a,uu____6113) ->
                                           let x_a =
                                             let uu____6119 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____6119
                                              in
                                           let res =
                                             let wp =
                                               let uu____6127 =
                                                 let uu____6132 =
                                                   let uu____6133 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6133
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____6142 =
                                                   let uu____6143 =
                                                     let uu____6152 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6152
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6161 =
                                                     let uu____6172 =
                                                       let uu____6181 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6181
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6172]  in
                                                   uu____6143 :: uu____6161
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____6132 uu____6142
                                                  in
                                               uu____6127
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____6217 =
                                               let uu____6226 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6233 =
                                                 let uu____6242 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____6242]  in
                                               uu____6226 :: uu____6233  in
                                             let uu____6267 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6217 uu____6267
                                              in
                                           let uu____6270 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____6270 with
                                            | (k1,uu____6278,uu____6279) ->
                                                let env1 =
                                                  let uu____6283 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____6283
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
                                          let uu____6294 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____6294
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____6295 = fresh_a_and_wp ()
                                           in
                                        match uu____6295 with
                                        | (a,wp_sort_a) ->
                                            let uu____6308 =
                                              fresh_a_and_wp ()  in
                                            (match uu____6308 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____6324 =
                                                     let uu____6333 =
                                                       let uu____6340 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____6340
                                                        in
                                                     [uu____6333]  in
                                                   let uu____6353 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6324 uu____6353
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
                                                   let uu____6361 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____6361
                                                    in
                                                 let wp_g_x =
                                                   let uu____6366 =
                                                     let uu____6371 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____6372 =
                                                       let uu____6373 =
                                                         let uu____6382 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6382
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____6373]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6371 uu____6372
                                                      in
                                                   uu____6366
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____6413 =
                                                       let uu____6418 =
                                                         let uu____6419 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6419
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____6428 =
                                                         let uu____6429 =
                                                           let uu____6432 =
                                                             let uu____6435 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____6436 =
                                                               let uu____6439
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____6440
                                                                 =
                                                                 let uu____6443
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____6444
                                                                   =
                                                                   let uu____6447
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____6447]
                                                                    in
                                                                 uu____6443
                                                                   ::
                                                                   uu____6444
                                                                  in
                                                               uu____6439 ::
                                                                 uu____6440
                                                                in
                                                             uu____6435 ::
                                                               uu____6436
                                                              in
                                                           r :: uu____6432
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6429
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____6418
                                                         uu____6428
                                                        in
                                                     uu____6413
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____6465 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____6465
                                                   then
                                                     let uu____6476 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____6483 =
                                                       let uu____6492 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____6492]  in
                                                     uu____6476 :: uu____6483
                                                   else []  in
                                                 let k =
                                                   let uu____6528 =
                                                     let uu____6537 =
                                                       let uu____6546 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____6553 =
                                                         let uu____6562 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____6562]  in
                                                       uu____6546 ::
                                                         uu____6553
                                                        in
                                                     let uu____6587 =
                                                       let uu____6596 =
                                                         let uu____6605 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____6612 =
                                                           let uu____6621 =
                                                             let uu____6628 =
                                                               let uu____6629
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____6629
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____6628
                                                              in
                                                           let uu____6630 =
                                                             let uu____6639 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____6646 =
                                                               let uu____6655
                                                                 =
                                                                 let uu____6662
                                                                   =
                                                                   let uu____6663
                                                                    =
                                                                    let uu____6672
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____6672]
                                                                     in
                                                                   let uu____6691
                                                                    =
                                                                    let uu____6694
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6694
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____6663
                                                                    uu____6691
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____6662
                                                                  in
                                                               [uu____6655]
                                                                in
                                                             uu____6639 ::
                                                               uu____6646
                                                              in
                                                           uu____6621 ::
                                                             uu____6630
                                                            in
                                                         uu____6605 ::
                                                           uu____6612
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____6596
                                                        in
                                                     FStar_List.append
                                                       uu____6537 uu____6587
                                                      in
                                                   let uu____6739 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6528 uu____6739
                                                    in
                                                 let uu____6742 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____6742 with
                                                  | (k1,uu____6750,uu____6751)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___713_6763
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___713_6763.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _6765  ->
                                                             FStar_Pervasives_Native.Some
                                                               _6765)
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
                                           (let uu____6792 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____6806 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____6806 with
                                                 | (usubst,uvs) ->
                                                     let uu____6829 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____6830 =
                                                       let uu___726_6831 =
                                                         act  in
                                                       let uu____6832 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6833 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___726_6831.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___726_6831.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___726_6831.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____6832;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____6833
                                                       }  in
                                                     (uu____6829, uu____6830))
                                               in
                                            match uu____6792 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____6837 =
                                                    let uu____6838 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____6838.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____6837 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____6864 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____6864
                                                      then
                                                        let uu____6867 =
                                                          let uu____6870 =
                                                            let uu____6871 =
                                                              let uu____6872
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____6872
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____6871
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____6870
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____6867
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6895 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6896 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____6896 with
                                                 | (act_typ1,uu____6904,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___743_6907 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___743_6907.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____6910 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6910
                                                       then
                                                         let uu____6914 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6916 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6918 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6914
                                                           uu____6916
                                                           uu____6918
                                                       else ());
                                                      (let uu____6923 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6923 with
                                                       | (act_defn,uu____6931,g_a)
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
                                                           let uu____6935 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____6971
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____6971
                                                                  with
                                                                  | (bs2,uu____6983)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6990
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6990
                                                                     in
                                                                    let uu____6993
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6993
                                                                    with
                                                                    | 
                                                                    (k1,uu____7007,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____7011 ->
                                                                 let uu____7012
                                                                   =
                                                                   let uu____7018
                                                                    =
                                                                    let uu____7020
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7022
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7020
                                                                    uu____7022
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7018)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____7012
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6935
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____7040
                                                                    =
                                                                    let uu____7041
                                                                    =
                                                                    let uu____7042
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7042
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7041
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____7040);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____7044
                                                                    =
                                                                    let uu____7045
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7045.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____7044
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7070
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7070
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7077
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7077
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7097
                                                                    =
                                                                    let uu____7098
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7098]
                                                                     in
                                                                    let uu____7099
                                                                    =
                                                                    let uu____7110
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7110]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7097;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7099;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7135
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7135))
                                                                    | 
                                                                    uu____7138
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____7140
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____7162
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7162))
                                                                     in
                                                                  match uu____7140
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
                                                                    let uu___793_7181
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___793_7181.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___793_7181.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___793_7181.FStar_Syntax_Syntax.action_params);
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
                             match uu____5738 with
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
                                   let uu____7206 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____7206 ts1
                                    in
                                 let ed3 =
                                   let uu___805_7216 = ed2  in
                                   let uu____7217 = cl signature  in
                                   let uu____7218 = cl ret_wp  in
                                   let uu____7219 = cl bind_wp  in
                                   let uu____7220 = cl stronger  in
                                   let uu____7221 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____7226 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____7229 = cl repr  in
                                   let uu____7230 = cl return_repr  in
                                   let uu____7231 = cl bind_repr  in
                                   let uu____7232 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___808_7240 = a  in
                                          let uu____7241 =
                                            let uu____7242 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____7242
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____7267 =
                                            let uu____7268 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____7268
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___808_7240.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___808_7240.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___808_7240.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___808_7240.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____7241;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____7267
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___805_7216.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___805_7216.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___805_7216.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___805_7216.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___805_7216.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____7217;
                                     FStar_Syntax_Syntax.ret_wp = uu____7218;
                                     FStar_Syntax_Syntax.bind_wp = uu____7219;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____7220;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____7221;
                                     FStar_Syntax_Syntax.trivial = uu____7226;
                                     FStar_Syntax_Syntax.repr = uu____7229;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____7230;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____7231;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____7232;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___805_7216.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____7294 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____7294
                                   then
                                     let uu____7299 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____7299
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
        let fail1 uu____7364 =
          let uu____7365 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____7371 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____7365 uu____7371  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____7415)::(wp,uu____7417)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____7446 -> fail1 ())
        | uu____7447 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____7460 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____7460
       then
         let uu____7465 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____7465
       else ());
      (let uu____7470 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____7470 with
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
             let uu____7503 =
               ((FStar_Pervasives_Native.fst
                   src_ed.FStar_Syntax_Syntax.is_layered)
                  &&
                  (let uu____7509 =
                     let uu____7510 =
                       FStar_All.pipe_right
                         src_ed.FStar_Syntax_Syntax.is_layered
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____7510 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____7509
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_Pervasives_Native.fst
                      tgt_ed.FStar_Syntax_Syntax.is_layered)
                     &&
                     (let uu____7531 =
                        let uu____7532 =
                          FStar_All.pipe_right
                            tgt_ed.FStar_Syntax_Syntax.is_layered
                            FStar_Pervasives_Native.snd
                           in
                        FStar_All.pipe_right uu____7532 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____7531
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____7550 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____7550))
                in
             if uu____7503
             then
               let uu____7553 =
                 let uu____7559 =
                   let uu____7561 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____7564 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____7561 uu____7564
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____7559)  in
               FStar_Errors.raise_error uu____7553 r
             else ());
            (let uu____7571 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____7595 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____7595 with
                  | (us1,lift1) ->
                      let uu____7610 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____7610, us1, lift1))
                in
             match uu____7571 with
             | (env,us1,lift1) ->
                 let uu____7620 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____7620 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____7633 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____7633
                         then
                           let uu____7638 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____7640 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____7638 uu____7640
                         else ());
                        (let lift_t_shape_error s =
                           let uu____7654 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____7656 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____7658 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____7654 uu____7656 s uu____7658
                            in
                         let uu____7661 =
                           let uu____7668 =
                             let uu____7673 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____7673
                               (fun uu____7690  ->
                                  match uu____7690 with
                                  | (t,u) ->
                                      let uu____7701 =
                                        let uu____7702 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____7702
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____7701, u))
                              in
                           match uu____7668 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____7721 =
                                   let uu____7722 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____7722.FStar_Syntax_Syntax.n  in
                                 match uu____7721 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____7734) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____7762 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____7762 with
                                      | (a',uu____7772)::bs1 ->
                                          let uu____7792 =
                                            let uu____7793 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____7793
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____7891 =
                                            let uu____7904 =
                                              let uu____7907 =
                                                let uu____7908 =
                                                  let uu____7915 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____7915)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____7908
                                                 in
                                              [uu____7907]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____7904
                                             in
                                          FStar_All.pipe_right uu____7792
                                            uu____7891)
                                 | uu____7930 ->
                                     let uu____7931 =
                                       let uu____7937 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____7937)
                                        in
                                     FStar_Errors.raise_error uu____7931 r
                                  in
                               let uu____7949 =
                                 let uu____7960 =
                                   let uu____7965 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____7972 =
                                     let uu____7973 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____7973
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____7965 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____7972
                                    in
                                 match uu____7960 with
                                 | (f_sort,g1) ->
                                     let uu____7994 =
                                       let uu____8001 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____8001
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____7994, g1)
                                  in
                               (match uu____7949 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____8068 =
                                      let uu____8073 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____8074 =
                                        let uu____8075 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____8075
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____8073 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____8074
                                       in
                                    (match uu____8068 with
                                     | (repr,g_repr) ->
                                         let uu____8092 =
                                           let uu____8095 =
                                             let uu____8098 =
                                               let uu____8101 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8101
                                                 (fun _8104  ->
                                                    FStar_Pervasives_Native.Some
                                                      _8104)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____8098
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____8095
                                            in
                                         let uu____8105 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____8092, uu____8105)))
                            in
                         match uu____7661 with
                         | (k,g_k) ->
                             ((let uu____8115 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____8115
                               then
                                 let uu____8120 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____8120
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____8129 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____8129
                                then
                                  let uu____8134 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____8134
                                else ());
                               (let uu____8139 =
                                  let uu____8152 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____8152 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____8179 =
                                            let uu____8185 =
                                              let uu____8187 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____8189 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____8191 =
                                                let uu____8193 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8193
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____8200 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____8187 uu____8189
                                                uu____8191 uu____8200
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____8185)
                                             in
                                          FStar_Errors.raise_error uu____8179
                                            r)
                                       else ();
                                       (let uu____8206 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____8215 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____8215 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____8206
                                        then
                                          let uu____8232 =
                                            let uu____8235 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____8235
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____8232)
                                        else
                                          (let uu____8246 =
                                             let uu____8252 =
                                               let uu____8254 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____8256 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____8258 =
                                                 let uu____8260 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8260
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____8267 =
                                                 let uu____8269 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8269
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____8276 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____8254 uu____8256
                                                 uu____8258 uu____8267
                                                 uu____8276
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____8252)
                                              in
                                           FStar_Errors.raise_error
                                             uu____8246 r)))
                                   in
                                match uu____8139 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___916_8308 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___916_8308.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___916_8308.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____8318 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____8318
                                      then
                                        let uu____8323 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____8323
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
          (let uu____8355 =
             let uu____8362 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8362
              in
           match uu____8355 with
           | (a,wp_a_src) ->
               let uu____8369 =
                 let uu____8376 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____8376
                  in
               (match uu____8369 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____8384 =
                        let uu____8387 =
                          let uu____8388 =
                            let uu____8395 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____8395)  in
                          FStar_Syntax_Syntax.NT uu____8388  in
                        [uu____8387]  in
                      FStar_Syntax_Subst.subst uu____8384 wp_b_tgt  in
                    let expected_k =
                      let uu____8403 =
                        let uu____8412 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____8419 =
                          let uu____8428 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____8428]  in
                        uu____8412 :: uu____8419  in
                      let uu____8453 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____8403 uu____8453  in
                    let repr_type eff_name a1 wp =
                      (let uu____8475 =
                         let uu____8477 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____8477  in
                       if uu____8475
                       then
                         let uu____8480 =
                           let uu____8486 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____8486)
                            in
                         let uu____8490 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____8480 uu____8490
                       else ());
                      (let uu____8493 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____8493 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____8526 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____8527 =
                             let uu____8534 =
                               let uu____8535 =
                                 let uu____8552 =
                                   let uu____8563 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____8572 =
                                     let uu____8583 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____8583]  in
                                   uu____8563 :: uu____8572  in
                                 (repr, uu____8552)  in
                               FStar_Syntax_Syntax.Tm_app uu____8535  in
                             FStar_Syntax_Syntax.mk uu____8534  in
                           uu____8527 FStar_Pervasives_Native.None uu____8526)
                       in
                    let uu____8628 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____8801 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____8812 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____8812 with
                              | (usubst,uvs1) ->
                                  let uu____8835 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8836 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8835, uu____8836)
                            else (env, lift_wp)  in
                          (match uu____8801 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8886 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8886))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8957 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8972 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8972 with
                              | (usubst,uvs) ->
                                  let uu____8997 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8997)
                            else ([], lift)  in
                          (match uu____8957 with
                           | (uvs,lift1) ->
                               ((let uu____9033 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9033
                                 then
                                   let uu____9037 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9037
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9043 =
                                   let uu____9050 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9050 lift1
                                    in
                                 match uu____9043 with
                                 | (lift2,comp,uu____9075) ->
                                     let uu____9076 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____9076 with
                                      | (uu____9105,lift_wp,lift_elab) ->
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
                                            let uu____9137 =
                                              let uu____9148 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____9148
                                               in
                                            let uu____9165 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____9137, uu____9165)
                                          else
                                            (let uu____9194 =
                                               let uu____9205 =
                                                 let uu____9214 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____9214)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9205
                                                in
                                             let uu____9229 =
                                               let uu____9238 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____9238)  in
                                             (uu____9194, uu____9229))))))
                       in
                    (match uu____8628 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___996_9302 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___996_9302.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___996_9302.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___996_9302.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___996_9302.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___996_9302.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___996_9302.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___996_9302.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___996_9302.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___996_9302.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___996_9302.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___996_9302.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___996_9302.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___996_9302.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___996_9302.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___996_9302.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___996_9302.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___996_9302.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___996_9302.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___996_9302.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___996_9302.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___996_9302.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___996_9302.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___996_9302.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___996_9302.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___996_9302.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___996_9302.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___996_9302.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___996_9302.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___996_9302.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___996_9302.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___996_9302.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___996_9302.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___996_9302.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___996_9302.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___996_9302.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___996_9302.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___996_9302.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___996_9302.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___996_9302.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___996_9302.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___996_9302.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___996_9302.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___996_9302.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___996_9302.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____9335 =
                                 let uu____9340 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9340 with
                                 | (usubst,uvs1) ->
                                     let uu____9363 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____9364 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____9363, uu____9364)
                                  in
                               (match uu____9335 with
                                | (env2,lift2) ->
                                    let uu____9369 =
                                      let uu____9376 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____9376
                                       in
                                    (match uu____9369 with
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
                                             let uu____9402 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____9403 =
                                               let uu____9410 =
                                                 let uu____9411 =
                                                   let uu____9428 =
                                                     let uu____9439 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____9448 =
                                                       let uu____9459 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____9459]  in
                                                     uu____9439 :: uu____9448
                                                      in
                                                   (lift_wp1, uu____9428)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____9411
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9410
                                                in
                                             uu____9403
                                               FStar_Pervasives_Native.None
                                               uu____9402
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____9507 =
                                             let uu____9516 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____9523 =
                                               let uu____9532 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____9539 =
                                                 let uu____9548 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____9548]  in
                                               uu____9532 :: uu____9539  in
                                             uu____9516 :: uu____9523  in
                                           let uu____9579 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____9507
                                             uu____9579
                                            in
                                         let uu____9582 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____9582 with
                                          | (expected_k2,uu____9592,uu____9593)
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
                                                   let uu____9601 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____9601))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____9609 =
                             let uu____9611 =
                               let uu____9613 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____9613
                                 FStar_List.length
                                in
                             uu____9611 <> Prims.int_one  in
                           if uu____9609
                           then
                             let uu____9636 =
                               let uu____9642 =
                                 let uu____9644 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9646 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9648 =
                                   let uu____9650 =
                                     let uu____9652 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9652
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9650
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9644 uu____9646 uu____9648
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9642)
                                in
                             FStar_Errors.raise_error uu____9636 r
                           else ());
                          (let uu____9679 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____9682 =
                                  let uu____9684 =
                                    let uu____9687 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____9687
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____9684
                                    FStar_List.length
                                   in
                                uu____9682 <> Prims.int_one)
                              in
                           if uu____9679
                           then
                             let uu____9725 =
                               let uu____9731 =
                                 let uu____9733 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9735 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9737 =
                                   let uu____9739 =
                                     let uu____9741 =
                                       let uu____9744 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____9744
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9741
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9739
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9733 uu____9735 uu____9737
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9731)
                                in
                             FStar_Errors.raise_error uu____9725 r
                           else ());
                          (let uu___1033_9786 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1033_9786.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1033_9786.FStar_Syntax_Syntax.target);
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
    fun uu____9817  ->
      fun r  ->
        match uu____9817 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9840 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9868 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9868 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9899 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9899 c  in
                     let uu____9908 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9908, uvs1, tps1, c1))
               in
            (match uu____9840 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9928 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9928 with
                  | (tps2,c2) ->
                      let uu____9943 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9943 with
                       | (tps3,env3,us) ->
                           let uu____9961 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____9961 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____9987)::uu____9988 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10007 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10015 =
                                    let uu____10017 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10017  in
                                  if uu____10015
                                  then
                                    let uu____10020 =
                                      let uu____10026 =
                                        let uu____10028 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10030 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10028 uu____10030
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10026)
                                       in
                                    FStar_Errors.raise_error uu____10020 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10038 =
                                    let uu____10039 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10039
                                     in
                                  match uu____10038 with
                                  | (uvs2,t) ->
                                      let uu____10068 =
                                        let uu____10073 =
                                          let uu____10086 =
                                            let uu____10087 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____10087.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____10086)  in
                                        match uu____10073 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____10102,c5)) -> ([], c5)
                                        | (uu____10144,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____10183 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____10068 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____10215 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____10215 with
                                               | (uu____10220,t1) ->
                                                   let uu____10222 =
                                                     let uu____10228 =
                                                       let uu____10230 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____10232 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____10236 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____10230
                                                         uu____10232
                                                         uu____10236
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____10228)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____10222 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  