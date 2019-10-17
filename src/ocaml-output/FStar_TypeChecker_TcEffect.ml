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
                  (let conjunction =
                     let conjunction_ts =
                       let uu____2752 =
                         FStar_All.pipe_right
                           ed.FStar_Syntax_Syntax.match_wps FStar_Util.right
                          in
                       uu____2752.FStar_Syntax_Syntax.conjunction  in
                     let r =
                       (FStar_Pervasives_Native.snd conjunction_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2762 =
                       check_and_gen "conjunction" Prims.int_one
                         conjunction_ts
                        in
                     match uu____2762 with
                     | (conjunction_us,conjunction_t,conjunction_ty) ->
                         let uu____2786 =
                           FStar_Syntax_Subst.open_univ_vars conjunction_us
                             conjunction_t
                            in
                         (match uu____2786 with
                          | (us,t) ->
                              let uu____2805 =
                                FStar_Syntax_Subst.open_univ_vars
                                  conjunction_us conjunction_ty
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
                                                "conjunction"
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
                                                             conjunction_us
                                                             uu____3333
                                                            in
                                                         (conjunction_us,
                                                           uu____3330,
                                                           conjunction_ty)))))))))
                      in
                   log_combinator "conjunction" conjunction;
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
                        (let uu____3365 =
                           let uu____3371 =
                             let uu____3373 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____3373
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____3371)
                            in
                         FStar_Errors.raise_error uu____3365 r)
                      else ();
                      (let uu____3380 =
                         let uu____3385 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____3385 with
                         | (usubst,us) ->
                             let uu____3408 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____3409 =
                               let uu___335_3410 = act  in
                               let uu____3411 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____3412 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___335_3410.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___335_3410.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___335_3410.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____3411;
                                 FStar_Syntax_Syntax.action_typ = uu____3412
                               }  in
                             (uu____3408, uu____3409)
                          in
                       match uu____3380 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____3416 =
                               let uu____3417 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____3417.FStar_Syntax_Syntax.n  in
                             match uu____3416 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____3443 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____3443
                                 then
                                   let repr_ts =
                                     let uu____3447 = repr  in
                                     match uu____3447 with
                                     | (us,t,uu____3462) -> (us, t)  in
                                   let repr1 =
                                     let uu____3480 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____3480
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____3492 =
                                       let uu____3497 =
                                         let uu____3498 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____3498 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____3497
                                        in
                                     uu____3492 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____3516 =
                                       let uu____3519 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____3519
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____3516
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____3522 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____3523 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____3523 with
                            | (act_typ1,uu____3531,g_t) ->
                                let uu____3533 =
                                  let uu____3540 =
                                    let uu___360_3541 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___360_3541.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___360_3541.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___360_3541.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___360_3541.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___360_3541.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___360_3541.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___360_3541.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___360_3541.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___360_3541.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___360_3541.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___360_3541.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___360_3541.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___360_3541.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___360_3541.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___360_3541.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___360_3541.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___360_3541.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___360_3541.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___360_3541.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___360_3541.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___360_3541.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___360_3541.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___360_3541.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___360_3541.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___360_3541.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___360_3541.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___360_3541.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___360_3541.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___360_3541.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___360_3541.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___360_3541.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___360_3541.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___360_3541.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___360_3541.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___360_3541.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___360_3541.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___360_3541.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___360_3541.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___360_3541.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___360_3541.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___360_3541.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___360_3541.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___360_3541.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___360_3541.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___360_3541.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____3540
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____3533 with
                                 | (act_defn,uu____3544,g_d) ->
                                     ((let uu____3547 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____3547
                                       then
                                         let uu____3552 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____3554 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____3552 uu____3554
                                       else ());
                                      (let uu____3559 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____3567 =
                                           let uu____3568 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____3568.FStar_Syntax_Syntax.n
                                            in
                                         match uu____3567 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____3578) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____3601 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____3601 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____3617 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____3617 with
                                                   | (a_tm,uu____3637,g_tm)
                                                       ->
                                                       let uu____3651 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____3651 with
                                                        | (repr1,g) ->
                                                            let uu____3664 =
                                                              let uu____3667
                                                                =
                                                                let uu____3670
                                                                  =
                                                                  let uu____3673
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____3673
                                                                    (
                                                                    fun _3676
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _3676)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____3670
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____3667
                                                               in
                                                            let uu____3677 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____3664,
                                                              uu____3677))))
                                         | uu____3680 ->
                                             let uu____3681 =
                                               let uu____3687 =
                                                 let uu____3689 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____3689
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____3687)
                                                in
                                             FStar_Errors.raise_error
                                               uu____3681 r
                                          in
                                       match uu____3559 with
                                       | (k,g_k) ->
                                           ((let uu____3706 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____3706
                                             then
                                               let uu____3711 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____3711
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____3719 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____3719
                                              then
                                                let uu____3724 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____3724
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____3737 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____3737
                                                   in
                                                let repr_args t =
                                                  let uu____3758 =
                                                    let uu____3759 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____3759.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____3758 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____3811 =
                                                        let uu____3812 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____3812.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____3811 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____3821,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____3831 ->
                                                           let uu____3832 =
                                                             let uu____3838 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____3838)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3832 r)
                                                  | uu____3847 ->
                                                      let uu____3848 =
                                                        let uu____3854 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____3854)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____3848 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____3864 =
                                                  let uu____3865 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____3865.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____3864 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____3890 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____3890 with
                                                     | (bs1,c1) ->
                                                         let uu____3897 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____3897
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
                                                              let uu____3908
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____3908))
                                                | uu____3911 ->
                                                    let uu____3912 =
                                                      let uu____3918 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____3918)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____3912 r
                                                 in
                                              (let uu____3922 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____3922
                                               then
                                                 let uu____3927 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____3927
                                               else ());
                                              (let act2 =
                                                 let uu____3933 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____3933 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___433_3947 =
                                                         act1  in
                                                       let uu____3948 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___433_3947.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___433_3947.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___433_3947.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____3948
                                                       }
                                                     else
                                                       (let uu____3951 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____3958
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____3958
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____3951
                                                        then
                                                          let uu___438_3963 =
                                                            act1  in
                                                          let uu____3964 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___438_3963.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___438_3963.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___438_3963.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___438_3963.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____3964
                                                          }
                                                        else
                                                          (let uu____3967 =
                                                             let uu____3973 =
                                                               let uu____3975
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____3977
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____3975
                                                                 uu____3977
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____3973)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____3967 r))
                                                  in
                                               act2)))))))))
                       in
                    let fst1 uu____4000 =
                      match uu____4000 with | (a,uu____4016,uu____4017) -> a
                       in
                    let snd1 uu____4049 =
                      match uu____4049 with | (uu____4064,b,uu____4066) -> b
                       in
                    let thd uu____4098 =
                      match uu____4098 with | (uu____4113,uu____4114,c) -> c
                       in
                    let uu___456_4128 = ed  in
                    let uu____4129 =
                      FStar_All.pipe_right
                        ((fst1 stronger_repr), (snd1 stronger_repr))
                        (fun _4138  -> FStar_Pervasives_Native.Some _4138)
                       in
                    let uu____4139 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.is_layered =
                        (true,
                          (FStar_Pervasives_Native.Some underlying_effect_lid));
                      FStar_Syntax_Syntax.cattributes =
                        (uu___456_4128.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.mname =
                        (uu___456_4128.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.univs =
                        (uu___456_4128.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___456_4128.FStar_Syntax_Syntax.binders);
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
                        (uu___456_4128.FStar_Syntax_Syntax.trivial);
                      FStar_Syntax_Syntax.repr = ((fst1 repr), (snd1 repr));
                      FStar_Syntax_Syntax.return_repr =
                        ((fst1 return_repr), (snd1 return_repr));
                      FStar_Syntax_Syntax.bind_repr =
                        ((fst1 bind_repr), (snd1 bind_repr));
                      FStar_Syntax_Syntax.stronger_repr = uu____4129;
                      FStar_Syntax_Syntax.actions = uu____4139;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___456_4128.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_check_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4194 =
          FStar_TypeChecker_TcTerm.tc_check_tot_or_gtot_term env t k  in
        match uu____4194 with
        | (t1,c,g) -> (FStar_TypeChecker_Rel.force_trivial_guard env g; t1)
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____4221 = tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____4221
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____4243 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____4243
         then
           let uu____4248 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____4248
         else ());
        (let uu____4254 =
           let uu____4259 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____4259 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____4283 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____4283  in
               let uu____4284 =
                 let uu____4291 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____4291 bs  in
               (match uu____4284 with
                | (bs1,uu____4297,uu____4298) ->
                    let uu____4299 =
                      let tmp_t =
                        let uu____4309 =
                          let uu____4312 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _4317  ->
                                 FStar_Pervasives_Native.Some _4317)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____4312
                           in
                        FStar_Syntax_Util.arrow bs1 uu____4309  in
                      let uu____4318 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____4318 with
                      | (us,tmp_t1) ->
                          let uu____4335 =
                            let uu____4336 =
                              let uu____4337 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____4337
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____4336
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____4335)
                       in
                    (match uu____4299 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____4406 ->
                              let uu____4409 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____4416 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____4416 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____4409
                              then (us, bs2)
                              else
                                (let uu____4427 =
                                   let uu____4433 =
                                     let uu____4435 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____4437 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____4435 uu____4437
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____4433)
                                    in
                                 let uu____4441 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____4427
                                   uu____4441))))
            in
         match uu____4254 with
         | (us,bs) ->
             let ed1 =
               let uu___497_4449 = ed  in
               {
                 FStar_Syntax_Syntax.is_layered =
                   (uu___497_4449.FStar_Syntax_Syntax.is_layered);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___497_4449.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.mname =
                   (uu___497_4449.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___497_4449.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.ret_wp =
                   (uu___497_4449.FStar_Syntax_Syntax.ret_wp);
                 FStar_Syntax_Syntax.bind_wp =
                   (uu___497_4449.FStar_Syntax_Syntax.bind_wp);
                 FStar_Syntax_Syntax.stronger =
                   (uu___497_4449.FStar_Syntax_Syntax.stronger);
                 FStar_Syntax_Syntax.match_wps =
                   (uu___497_4449.FStar_Syntax_Syntax.match_wps);
                 FStar_Syntax_Syntax.trivial =
                   (uu___497_4449.FStar_Syntax_Syntax.trivial);
                 FStar_Syntax_Syntax.repr =
                   (uu___497_4449.FStar_Syntax_Syntax.repr);
                 FStar_Syntax_Syntax.return_repr =
                   (uu___497_4449.FStar_Syntax_Syntax.return_repr);
                 FStar_Syntax_Syntax.bind_repr =
                   (uu___497_4449.FStar_Syntax_Syntax.bind_repr);
                 FStar_Syntax_Syntax.stronger_repr =
                   (uu___497_4449.FStar_Syntax_Syntax.stronger_repr);
                 FStar_Syntax_Syntax.actions =
                   (uu___497_4449.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___497_4449.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____4450 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____4450 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____4469 =
                    let uu____4474 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____4474  in
                  (match uu____4469 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____4495 =
                           match uu____4495 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____4515 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4515 t  in
                               let uu____4524 =
                                 let uu____4525 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____4525 t1  in
                               (us1, uu____4524)
                            in
                         let uu___511_4530 = ed1  in
                         let uu____4531 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____4532 = op ed1.FStar_Syntax_Syntax.ret_wp
                            in
                         let uu____4533 = op ed1.FStar_Syntax_Syntax.bind_wp
                            in
                         let uu____4534 = op ed1.FStar_Syntax_Syntax.stronger
                            in
                         let uu____4535 =
                           FStar_Syntax_Util.map_match_wps op
                             ed1.FStar_Syntax_Syntax.match_wps
                            in
                         let uu____4540 =
                           FStar_Util.map_opt ed1.FStar_Syntax_Syntax.trivial
                             op
                            in
                         let uu____4543 = op ed1.FStar_Syntax_Syntax.repr  in
                         let uu____4544 =
                           op ed1.FStar_Syntax_Syntax.return_repr  in
                         let uu____4545 =
                           op ed1.FStar_Syntax_Syntax.bind_repr  in
                         let uu____4546 =
                           FStar_List.map
                             (fun a  ->
                                let uu___514_4554 = a  in
                                let uu____4555 =
                                  let uu____4556 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____4556  in
                                let uu____4567 =
                                  let uu____4568 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____4568  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___514_4554.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___514_4554.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___514_4554.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___514_4554.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____4555;
                                  FStar_Syntax_Syntax.action_typ = uu____4567
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.is_layered =
                             (uu___511_4530.FStar_Syntax_Syntax.is_layered);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___511_4530.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.mname =
                             (uu___511_4530.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.univs =
                             (uu___511_4530.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___511_4530.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____4531;
                           FStar_Syntax_Syntax.ret_wp = uu____4532;
                           FStar_Syntax_Syntax.bind_wp = uu____4533;
                           FStar_Syntax_Syntax.stronger = uu____4534;
                           FStar_Syntax_Syntax.match_wps = uu____4535;
                           FStar_Syntax_Syntax.trivial = uu____4540;
                           FStar_Syntax_Syntax.repr = uu____4543;
                           FStar_Syntax_Syntax.return_repr = uu____4544;
                           FStar_Syntax_Syntax.bind_repr = uu____4545;
                           FStar_Syntax_Syntax.stronger_repr =
                             FStar_Pervasives_Native.None;
                           FStar_Syntax_Syntax.actions = uu____4546;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___511_4530.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____4580 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____4580
                         then
                           let uu____4585 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____4585
                         else ());
                        (let env =
                           let uu____4592 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____4592
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____4627 k =
                           match uu____4627 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____4647 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____4647 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____4656 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          tc_check_trivial_guard uu____4656
                                            t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____4657 =
                                            let uu____4664 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____4664 t1
                                             in
                                          (match uu____4657 with
                                           | (t2,uu____4666,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____4669 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____4669 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____4685 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____4687 =
                                                 let uu____4689 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____4689
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____4685 uu____4687
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____4704 ->
                                               let uu____4705 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____4712 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____4712 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____4705
                                               then (g_us, t3)
                                               else
                                                 (let uu____4723 =
                                                    let uu____4729 =
                                                      let uu____4731 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____4733 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____4731
                                                        uu____4733
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____4729)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____4723
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____4741 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____4741
                          then
                            let uu____4746 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____4746
                          else ());
                         (let fresh_a_and_wp uu____4762 =
                            let fail1 t =
                              let uu____4775 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____4775
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____4791 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____4791 with
                            | (uu____4802,signature1) ->
                                let uu____4804 =
                                  let uu____4805 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____4805.FStar_Syntax_Syntax.n  in
                                (match uu____4804 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____4815) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____4844)::(wp,uu____4846)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____4875 -> fail1 signature1)
                                 | uu____4876 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____4890 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____4890
                            then
                              let uu____4895 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____4895
                            else ()  in
                          let ret_wp =
                            let uu____4901 = fresh_a_and_wp ()  in
                            match uu____4901 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____4917 =
                                    let uu____4926 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____4933 =
                                      let uu____4942 =
                                        let uu____4949 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____4949
                                         in
                                      [uu____4942]  in
                                    uu____4926 :: uu____4933  in
                                  let uu____4968 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____4917
                                    uu____4968
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None
                                  ed2.FStar_Syntax_Syntax.ret_wp
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____4976 = fresh_a_and_wp ()  in
                             match uu____4976 with
                             | (a,wp_sort_a) ->
                                 let uu____4989 = fresh_a_and_wp ()  in
                                 (match uu____4989 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5005 =
                                          let uu____5014 =
                                            let uu____5021 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5021
                                             in
                                          [uu____5014]  in
                                        let uu____5034 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5005
                                          uu____5034
                                         in
                                      let k =
                                        let uu____5040 =
                                          let uu____5049 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5056 =
                                            let uu____5065 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5072 =
                                              let uu____5081 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5088 =
                                                let uu____5097 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5104 =
                                                  let uu____5113 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5113]  in
                                                uu____5097 :: uu____5104  in
                                              uu____5081 :: uu____5088  in
                                            uu____5065 :: uu____5072  in
                                          uu____5049 :: uu____5056  in
                                        let uu____5156 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5040
                                          uu____5156
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        ed2.FStar_Syntax_Syntax.bind_wp
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5164 = fresh_a_and_wp ()  in
                              match uu____5164 with
                              | (a,wp_sort_a) ->
                                  let uu____5177 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____5177 with
                                   | (t,uu____5183) ->
                                       let k =
                                         let uu____5187 =
                                           let uu____5196 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____5203 =
                                             let uu____5212 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____5219 =
                                               let uu____5228 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____5228]  in
                                             uu____5212 :: uu____5219  in
                                           uu____5196 :: uu____5203  in
                                         let uu____5259 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____5187
                                           uu____5259
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         ed2.FStar_Syntax_Syntax.stronger
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let match_wps =
                               let uu____5271 =
                                 FStar_Syntax_Util.get_match_with_close_wps
                                   ed2.FStar_Syntax_Syntax.match_wps
                                  in
                               match uu____5271 with
                               | (if_then_else1,ite_wp,close_wp) ->
                                   let if_then_else2 =
                                     let uu____5286 = fresh_a_and_wp ()  in
                                     match uu____5286 with
                                     | (a,wp_sort_a) ->
                                         let p =
                                           let uu____5300 =
                                             let uu____5303 =
                                               FStar_Ident.range_of_lid
                                                 ed2.FStar_Syntax_Syntax.mname
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____5303
                                              in
                                           let uu____5304 =
                                             let uu____5305 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_right uu____5305
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_Syntax_Syntax.new_bv
                                             uu____5300 uu____5304
                                            in
                                         let k =
                                           let uu____5317 =
                                             let uu____5326 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a
                                                in
                                             let uu____5333 =
                                               let uu____5342 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   p
                                                  in
                                               let uu____5349 =
                                                 let uu____5358 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 let uu____5365 =
                                                   let uu____5374 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a
                                                      in
                                                   [uu____5374]  in
                                                 uu____5358 :: uu____5365  in
                                               uu____5342 :: uu____5349  in
                                             uu____5326 :: uu____5333  in
                                           let uu____5411 =
                                             FStar_Syntax_Syntax.mk_Total
                                               wp_sort_a
                                              in
                                           FStar_Syntax_Util.arrow uu____5317
                                             uu____5411
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
                                       let uu____5419 = fresh_a_and_wp ()  in
                                       match uu____5419 with
                                       | (a,wp_sort_a) ->
                                           let k =
                                             let uu____5435 =
                                               let uu____5444 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____5451 =
                                                 let uu____5460 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____5460]  in
                                               uu____5444 :: uu____5451  in
                                             let uu____5485 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 wp_sort_a
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____5435 uu____5485
                                              in
                                           check_and_gen' "ite_wp"
                                             Prims.int_one
                                             FStar_Pervasives_Native.None
                                             ite_wp
                                             (FStar_Pervasives_Native.Some k)
                                        in
                                     log_combinator "ite_wp" ite_wp1;
                                     (let close_wp1 =
                                        let uu____5493 = fresh_a_and_wp ()
                                           in
                                        match uu____5493 with
                                        | (a,wp_sort_a) ->
                                            let b =
                                              let uu____5507 =
                                                let uu____5510 =
                                                  FStar_Ident.range_of_lid
                                                    ed2.FStar_Syntax_Syntax.mname
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____5510
                                                 in
                                              let uu____5511 =
                                                let uu____5512 =
                                                  FStar_Syntax_Util.type_u ()
                                                   in
                                                FStar_All.pipe_right
                                                  uu____5512
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_Syntax_Syntax.new_bv
                                                uu____5507 uu____5511
                                               in
                                            let wp_sort_b_a =
                                              let uu____5524 =
                                                let uu____5533 =
                                                  let uu____5540 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      b
                                                     in
                                                  FStar_Syntax_Syntax.null_binder
                                                    uu____5540
                                                   in
                                                [uu____5533]  in
                                              let uu____5553 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5524 uu____5553
                                               in
                                            let k =
                                              let uu____5559 =
                                                let uu____5568 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    a
                                                   in
                                                let uu____5575 =
                                                  let uu____5584 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      b
                                                     in
                                                  let uu____5591 =
                                                    let uu____5600 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_b_a
                                                       in
                                                    [uu____5600]  in
                                                  uu____5584 :: uu____5591
                                                   in
                                                uu____5568 :: uu____5575  in
                                              let uu____5631 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  wp_sort_a
                                                 in
                                              FStar_Syntax_Util.arrow
                                                uu____5559 uu____5631
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
                               let uu____5641 = fresh_a_and_wp ()  in
                               match uu____5641 with
                               | (a,wp_sort_a) ->
                                   let uu____5656 =
                                     FStar_Syntax_Util.type_u ()  in
                                   (match uu____5656 with
                                    | (t,uu____5664) ->
                                        let k =
                                          let uu____5668 =
                                            let uu____5677 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5684 =
                                              let uu____5693 =
                                                FStar_Syntax_Syntax.null_binder
                                                  wp_sort_a
                                                 in
                                              [uu____5693]  in
                                            uu____5677 :: uu____5684  in
                                          let uu____5718 =
                                            FStar_Syntax_Syntax.mk_GTotal t
                                             in
                                          FStar_Syntax_Util.arrow uu____5668
                                            uu____5718
                                           in
                                        let trivial =
                                          let uu____5722 =
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.trivial
                                              FStar_Util.must
                                             in
                                          check_and_gen' "trivial"
                                            Prims.int_one
                                            FStar_Pervasives_Native.None
                                            uu____5722
                                            (FStar_Pervasives_Native.Some k)
                                           in
                                        (log_combinator "trivial" trivial;
                                         FStar_Pervasives_Native.Some trivial))
                                in
                             let uu____5737 =
                               let uu____5748 =
                                 let uu____5749 =
                                   FStar_Syntax_Subst.compress
                                     (FStar_Pervasives_Native.snd
                                        ed2.FStar_Syntax_Syntax.repr)
                                    in
                                 uu____5749.FStar_Syntax_Syntax.n  in
                               match uu____5748 with
                               | FStar_Syntax_Syntax.Tm_unknown  ->
                                   ((ed2.FStar_Syntax_Syntax.repr),
                                     (ed2.FStar_Syntax_Syntax.return_repr),
                                     (ed2.FStar_Syntax_Syntax.bind_repr),
                                     (ed2.FStar_Syntax_Syntax.actions))
                               | uu____5768 ->
                                   let repr =
                                     let uu____5770 = fresh_a_and_wp ()  in
                                     match uu____5770 with
                                     | (a,wp_sort_a) ->
                                         let uu____5783 =
                                           FStar_Syntax_Util.type_u ()  in
                                         (match uu____5783 with
                                          | (t,uu____5789) ->
                                              let k =
                                                let uu____5793 =
                                                  let uu____5802 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____5809 =
                                                    let uu____5818 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a
                                                       in
                                                    [uu____5818]  in
                                                  uu____5802 :: uu____5809
                                                   in
                                                let uu____5843 =
                                                  FStar_Syntax_Syntax.mk_GTotal
                                                    t
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____5793 uu____5843
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
                                       let uu____5863 =
                                         FStar_TypeChecker_Env.inst_tscheme
                                           repr
                                          in
                                       match uu____5863 with
                                       | (uu____5870,repr1) ->
                                           let repr2 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env repr1
                                              in
                                           let uu____5873 =
                                             let uu____5880 =
                                               let uu____5881 =
                                                 let uu____5898 =
                                                   let uu____5909 =
                                                     FStar_All.pipe_right t
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____5926 =
                                                     let uu____5937 =
                                                       FStar_All.pipe_right
                                                         wp
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____5937]  in
                                                   uu____5909 :: uu____5926
                                                    in
                                                 (repr2, uu____5898)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____5881
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____5880
                                              in
                                           uu____5873
                                             FStar_Pervasives_Native.None
                                             FStar_Range.dummyRange
                                        in
                                     let mk_repr a wp =
                                       let uu____6003 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       mk_repr' uu____6003 wp  in
                                     let destruct_repr t =
                                       let uu____6018 =
                                         let uu____6019 =
                                           FStar_Syntax_Subst.compress t  in
                                         uu____6019.FStar_Syntax_Syntax.n  in
                                       match uu____6018 with
                                       | FStar_Syntax_Syntax.Tm_app
                                           (uu____6030,(t1,uu____6032)::
                                            (wp,uu____6034)::[])
                                           -> (t1, wp)
                                       | uu____6093 ->
                                           failwith "Unexpected repr type"
                                        in
                                     let return_repr =
                                       let uu____6104 = fresh_a_and_wp ()  in
                                       match uu____6104 with
                                       | (a,uu____6112) ->
                                           let x_a =
                                             let uu____6118 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.gen_bv "x_a"
                                               FStar_Pervasives_Native.None
                                               uu____6118
                                              in
                                           let res =
                                             let wp =
                                               let uu____6126 =
                                                 let uu____6131 =
                                                   let uu____6132 =
                                                     FStar_TypeChecker_Env.inst_tscheme
                                                       ret_wp
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6132
                                                     FStar_Pervasives_Native.snd
                                                    in
                                                 let uu____6141 =
                                                   let uu____6142 =
                                                     let uu____6151 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         a
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____6151
                                                       FStar_Syntax_Syntax.as_arg
                                                      in
                                                   let uu____6160 =
                                                     let uu____6171 =
                                                       let uu____6180 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           x_a
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____6180
                                                         FStar_Syntax_Syntax.as_arg
                                                        in
                                                     [uu____6171]  in
                                                   uu____6142 :: uu____6160
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   uu____6131 uu____6141
                                                  in
                                               uu____6126
                                                 FStar_Pervasives_Native.None
                                                 FStar_Range.dummyRange
                                                in
                                             mk_repr a wp  in
                                           let k =
                                             let uu____6216 =
                                               let uu____6225 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6232 =
                                                 let uu____6241 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     x_a
                                                    in
                                                 [uu____6241]  in
                                               uu____6225 :: uu____6232  in
                                             let uu____6266 =
                                               FStar_Syntax_Syntax.mk_Total
                                                 res
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6216 uu____6266
                                              in
                                           let uu____6269 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env k
                                              in
                                           (match uu____6269 with
                                            | (k1,uu____6277,uu____6278) ->
                                                let env1 =
                                                  let uu____6282 =
                                                    FStar_TypeChecker_Env.set_range
                                                      env
                                                      (FStar_Pervasives_Native.snd
                                                         ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____6282
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
                                          let uu____6293 =
                                            FStar_Syntax_Syntax.lid_as_fv
                                              FStar_Parser_Const.range_0
                                              FStar_Syntax_Syntax.delta_constant
                                              FStar_Pervasives_Native.None
                                             in
                                          FStar_All.pipe_right uu____6293
                                            FStar_Syntax_Syntax.fv_to_tm
                                           in
                                        let uu____6294 = fresh_a_and_wp ()
                                           in
                                        match uu____6294 with
                                        | (a,wp_sort_a) ->
                                            let uu____6307 =
                                              fresh_a_and_wp ()  in
                                            (match uu____6307 with
                                             | (b,wp_sort_b) ->
                                                 let wp_sort_a_b =
                                                   let uu____6323 =
                                                     let uu____6332 =
                                                       let uu____6339 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           a
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____6339
                                                        in
                                                     [uu____6332]  in
                                                   let uu____6352 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       wp_sort_b
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6323 uu____6352
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
                                                   let uu____6360 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "x_a"
                                                     FStar_Pervasives_Native.None
                                                     uu____6360
                                                    in
                                                 let wp_g_x =
                                                   let uu____6365 =
                                                     let uu____6370 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_g
                                                        in
                                                     let uu____6371 =
                                                       let uu____6372 =
                                                         let uu____6381 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             x_a
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6381
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____6372]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       uu____6370 uu____6371
                                                      in
                                                   uu____6365
                                                     FStar_Pervasives_Native.None
                                                     FStar_Range.dummyRange
                                                    in
                                                 let res =
                                                   let wp =
                                                     let uu____6412 =
                                                       let uu____6417 =
                                                         let uu____6418 =
                                                           FStar_TypeChecker_Env.inst_tscheme
                                                             bind_wp
                                                            in
                                                         FStar_All.pipe_right
                                                           uu____6418
                                                           FStar_Pervasives_Native.snd
                                                          in
                                                       let uu____6427 =
                                                         let uu____6428 =
                                                           let uu____6431 =
                                                             let uu____6434 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 a
                                                                in
                                                             let uu____6435 =
                                                               let uu____6438
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   b
                                                                  in
                                                               let uu____6439
                                                                 =
                                                                 let uu____6442
                                                                   =
                                                                   FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f
                                                                    in
                                                                 let uu____6443
                                                                   =
                                                                   let uu____6446
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                   [uu____6446]
                                                                    in
                                                                 uu____6442
                                                                   ::
                                                                   uu____6443
                                                                  in
                                                               uu____6438 ::
                                                                 uu____6439
                                                                in
                                                             uu____6434 ::
                                                               uu____6435
                                                              in
                                                           r :: uu____6431
                                                            in
                                                         FStar_List.map
                                                           FStar_Syntax_Syntax.as_arg
                                                           uu____6428
                                                          in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____6417
                                                         uu____6427
                                                        in
                                                     uu____6412
                                                       FStar_Pervasives_Native.None
                                                       FStar_Range.dummyRange
                                                      in
                                                   mk_repr b wp  in
                                                 let maybe_range_arg =
                                                   let uu____6464 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed2.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____6464
                                                   then
                                                     let uu____6475 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         FStar_Syntax_Syntax.t_range
                                                        in
                                                     let uu____6482 =
                                                       let uu____6491 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           FStar_Syntax_Syntax.t_range
                                                          in
                                                       [uu____6491]  in
                                                     uu____6475 :: uu____6482
                                                   else []  in
                                                 let k =
                                                   let uu____6527 =
                                                     let uu____6536 =
                                                       let uu____6545 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a
                                                          in
                                                       let uu____6552 =
                                                         let uu____6561 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             b
                                                            in
                                                         [uu____6561]  in
                                                       uu____6545 ::
                                                         uu____6552
                                                        in
                                                     let uu____6586 =
                                                       let uu____6595 =
                                                         let uu____6604 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             wp_f
                                                            in
                                                         let uu____6611 =
                                                           let uu____6620 =
                                                             let uu____6627 =
                                                               let uu____6628
                                                                 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   wp_f
                                                                  in
                                                               mk_repr a
                                                                 uu____6628
                                                                in
                                                             FStar_Syntax_Syntax.null_binder
                                                               uu____6627
                                                              in
                                                           let uu____6629 =
                                                             let uu____6638 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp_g
                                                                in
                                                             let uu____6645 =
                                                               let uu____6654
                                                                 =
                                                                 let uu____6661
                                                                   =
                                                                   let uu____6662
                                                                    =
                                                                    let uu____6671
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____6671]
                                                                     in
                                                                   let uu____6690
                                                                    =
                                                                    let uu____6693
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____6693
                                                                     in
                                                                   FStar_Syntax_Util.arrow
                                                                    uu____6662
                                                                    uu____6690
                                                                    in
                                                                 FStar_Syntax_Syntax.null_binder
                                                                   uu____6661
                                                                  in
                                                               [uu____6654]
                                                                in
                                                             uu____6638 ::
                                                               uu____6645
                                                              in
                                                           uu____6620 ::
                                                             uu____6629
                                                            in
                                                         uu____6604 ::
                                                           uu____6611
                                                          in
                                                       FStar_List.append
                                                         maybe_range_arg
                                                         uu____6595
                                                        in
                                                     FStar_List.append
                                                       uu____6536 uu____6586
                                                      in
                                                   let uu____6738 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       res
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6527 uu____6738
                                                    in
                                                 let uu____6741 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env k
                                                    in
                                                 (match uu____6741 with
                                                  | (k1,uu____6749,uu____6750)
                                                      ->
                                                      let env1 =
                                                        FStar_TypeChecker_Env.set_range
                                                          env
                                                          (FStar_Pervasives_Native.snd
                                                             ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                                         in
                                                      let env2 =
                                                        FStar_All.pipe_right
                                                          (let uu___712_6762
                                                             = env1  in
                                                           {
                                                             FStar_TypeChecker_Env.solver
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.solver);
                                                             FStar_TypeChecker_Env.range
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.range);
                                                             FStar_TypeChecker_Env.curmodule
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.curmodule);
                                                             FStar_TypeChecker_Env.gamma
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.gamma);
                                                             FStar_TypeChecker_Env.gamma_sig
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.gamma_sig);
                                                             FStar_TypeChecker_Env.gamma_cache
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.gamma_cache);
                                                             FStar_TypeChecker_Env.modules
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.modules);
                                                             FStar_TypeChecker_Env.expected_typ
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.expected_typ);
                                                             FStar_TypeChecker_Env.sigtab
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.sigtab);
                                                             FStar_TypeChecker_Env.attrtab
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.attrtab);
                                                             FStar_TypeChecker_Env.instantiate_imp
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.instantiate_imp);
                                                             FStar_TypeChecker_Env.effects
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.effects);
                                                             FStar_TypeChecker_Env.generalize
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.generalize);
                                                             FStar_TypeChecker_Env.letrecs
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.letrecs);
                                                             FStar_TypeChecker_Env.top_level
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.top_level);
                                                             FStar_TypeChecker_Env.check_uvars
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.check_uvars);
                                                             FStar_TypeChecker_Env.use_eq
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.use_eq);
                                                             FStar_TypeChecker_Env.is_iface
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.is_iface);
                                                             FStar_TypeChecker_Env.admit
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.admit);
                                                             FStar_TypeChecker_Env.lax
                                                               = true;
                                                             FStar_TypeChecker_Env.lax_universes
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.lax_universes);
                                                             FStar_TypeChecker_Env.phase1
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.phase1);
                                                             FStar_TypeChecker_Env.failhard
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.failhard);
                                                             FStar_TypeChecker_Env.nosynth
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.nosynth);
                                                             FStar_TypeChecker_Env.uvar_subtyping
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.uvar_subtyping);
                                                             FStar_TypeChecker_Env.tc_term
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.tc_term);
                                                             FStar_TypeChecker_Env.type_of
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.type_of);
                                                             FStar_TypeChecker_Env.universe_of
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.universe_of);
                                                             FStar_TypeChecker_Env.check_type_of
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.check_type_of);
                                                             FStar_TypeChecker_Env.use_bv_sorts
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.use_bv_sorts);
                                                             FStar_TypeChecker_Env.qtbl_name_and_index
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                             FStar_TypeChecker_Env.normalized_eff_names
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.normalized_eff_names);
                                                             FStar_TypeChecker_Env.fv_delta_depths
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.fv_delta_depths);
                                                             FStar_TypeChecker_Env.proof_ns
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.proof_ns);
                                                             FStar_TypeChecker_Env.synth_hook
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.synth_hook);
                                                             FStar_TypeChecker_Env.try_solve_implicits_hook
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                             FStar_TypeChecker_Env.splice
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.splice);
                                                             FStar_TypeChecker_Env.mpreprocess
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.mpreprocess);
                                                             FStar_TypeChecker_Env.postprocess
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.postprocess);
                                                             FStar_TypeChecker_Env.is_native_tactic
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.is_native_tactic);
                                                             FStar_TypeChecker_Env.identifier_info
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.identifier_info);
                                                             FStar_TypeChecker_Env.tc_hooks
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.tc_hooks);
                                                             FStar_TypeChecker_Env.dsenv
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.dsenv);
                                                             FStar_TypeChecker_Env.nbe
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.nbe);
                                                             FStar_TypeChecker_Env.strict_args_tab
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.strict_args_tab);
                                                             FStar_TypeChecker_Env.erasable_types_tab
                                                               =
                                                               (uu___712_6762.FStar_TypeChecker_Env.erasable_types_tab)
                                                           })
                                                          (fun _6764  ->
                                                             FStar_Pervasives_Native.Some
                                                               _6764)
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
                                           (let uu____6791 =
                                              if
                                                act.FStar_Syntax_Syntax.action_univs
                                                  = []
                                              then (env, act)
                                              else
                                                (let uu____6805 =
                                                   FStar_Syntax_Subst.univ_var_opening
                                                     act.FStar_Syntax_Syntax.action_univs
                                                    in
                                                 match uu____6805 with
                                                 | (usubst,uvs) ->
                                                     let uu____6828 =
                                                       FStar_TypeChecker_Env.push_univ_vars
                                                         env uvs
                                                        in
                                                     let uu____6829 =
                                                       let uu___725_6830 =
                                                         act  in
                                                       let uu____6831 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       let uu____6832 =
                                                         FStar_Syntax_Subst.subst
                                                           usubst
                                                           act.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___725_6830.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___725_6830.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = uvs;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___725_6830.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = uu____6831;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____6832
                                                       }  in
                                                     (uu____6828, uu____6829))
                                               in
                                            match uu____6791 with
                                            | (env1,act1) ->
                                                let act_typ =
                                                  let uu____6836 =
                                                    let uu____6837 =
                                                      FStar_Syntax_Subst.compress
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                       in
                                                    uu____6837.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____6836 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1,c) ->
                                                      let c1 =
                                                        FStar_Syntax_Util.comp_to_comp_typ
                                                          c
                                                         in
                                                      let uu____6863 =
                                                        FStar_Ident.lid_equals
                                                          c1.FStar_Syntax_Syntax.effect_name
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      if uu____6863
                                                      then
                                                        let uu____6866 =
                                                          let uu____6869 =
                                                            let uu____6870 =
                                                              let uu____6871
                                                                =
                                                                FStar_List.hd
                                                                  c1.FStar_Syntax_Syntax.effect_args
                                                                 in
                                                              FStar_Pervasives_Native.fst
                                                                uu____6871
                                                               in
                                                            mk_repr'
                                                              c1.FStar_Syntax_Syntax.result_typ
                                                              uu____6870
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total
                                                            uu____6869
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          bs1 uu____6866
                                                      else
                                                        act1.FStar_Syntax_Syntax.action_typ
                                                  | uu____6894 ->
                                                      act1.FStar_Syntax_Syntax.action_typ
                                                   in
                                                let uu____6895 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env1 act_typ
                                                   in
                                                (match uu____6895 with
                                                 | (act_typ1,uu____6903,g_t)
                                                     ->
                                                     let env' =
                                                       let uu___742_6906 =
                                                         FStar_TypeChecker_Env.set_expected_typ
                                                           env1 act_typ1
                                                          in
                                                       {
                                                         FStar_TypeChecker_Env.solver
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.solver);
                                                         FStar_TypeChecker_Env.range
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.range);
                                                         FStar_TypeChecker_Env.curmodule
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.curmodule);
                                                         FStar_TypeChecker_Env.gamma
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.gamma);
                                                         FStar_TypeChecker_Env.gamma_sig
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.gamma_sig);
                                                         FStar_TypeChecker_Env.gamma_cache
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.gamma_cache);
                                                         FStar_TypeChecker_Env.modules
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.modules);
                                                         FStar_TypeChecker_Env.expected_typ
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.expected_typ);
                                                         FStar_TypeChecker_Env.sigtab
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.sigtab);
                                                         FStar_TypeChecker_Env.attrtab
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.attrtab);
                                                         FStar_TypeChecker_Env.instantiate_imp
                                                           = false;
                                                         FStar_TypeChecker_Env.effects
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.effects);
                                                         FStar_TypeChecker_Env.generalize
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.generalize);
                                                         FStar_TypeChecker_Env.letrecs
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.letrecs);
                                                         FStar_TypeChecker_Env.top_level
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.top_level);
                                                         FStar_TypeChecker_Env.check_uvars
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.check_uvars);
                                                         FStar_TypeChecker_Env.use_eq
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.use_eq);
                                                         FStar_TypeChecker_Env.is_iface
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.is_iface);
                                                         FStar_TypeChecker_Env.admit
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.admit);
                                                         FStar_TypeChecker_Env.lax
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.lax);
                                                         FStar_TypeChecker_Env.lax_universes
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.lax_universes);
                                                         FStar_TypeChecker_Env.phase1
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.phase1);
                                                         FStar_TypeChecker_Env.failhard
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.failhard);
                                                         FStar_TypeChecker_Env.nosynth
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.nosynth);
                                                         FStar_TypeChecker_Env.uvar_subtyping
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.uvar_subtyping);
                                                         FStar_TypeChecker_Env.tc_term
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.tc_term);
                                                         FStar_TypeChecker_Env.type_of
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.type_of);
                                                         FStar_TypeChecker_Env.universe_of
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.universe_of);
                                                         FStar_TypeChecker_Env.check_type_of
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.check_type_of);
                                                         FStar_TypeChecker_Env.use_bv_sorts
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.use_bv_sorts);
                                                         FStar_TypeChecker_Env.qtbl_name_and_index
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                         FStar_TypeChecker_Env.normalized_eff_names
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.normalized_eff_names);
                                                         FStar_TypeChecker_Env.fv_delta_depths
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.fv_delta_depths);
                                                         FStar_TypeChecker_Env.proof_ns
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.proof_ns);
                                                         FStar_TypeChecker_Env.synth_hook
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.synth_hook);
                                                         FStar_TypeChecker_Env.try_solve_implicits_hook
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                         FStar_TypeChecker_Env.splice
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.splice);
                                                         FStar_TypeChecker_Env.mpreprocess
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.mpreprocess);
                                                         FStar_TypeChecker_Env.postprocess
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.postprocess);
                                                         FStar_TypeChecker_Env.is_native_tactic
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.is_native_tactic);
                                                         FStar_TypeChecker_Env.identifier_info
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.identifier_info);
                                                         FStar_TypeChecker_Env.tc_hooks
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.tc_hooks);
                                                         FStar_TypeChecker_Env.dsenv
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.dsenv);
                                                         FStar_TypeChecker_Env.nbe
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.nbe);
                                                         FStar_TypeChecker_Env.strict_args_tab
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.strict_args_tab);
                                                         FStar_TypeChecker_Env.erasable_types_tab
                                                           =
                                                           (uu___742_6906.FStar_TypeChecker_Env.erasable_types_tab)
                                                       }  in
                                                     ((let uu____6909 =
                                                         FStar_TypeChecker_Env.debug
                                                           env1
                                                           (FStar_Options.Other
                                                              "ED")
                                                          in
                                                       if uu____6909
                                                       then
                                                         let uu____6913 =
                                                           FStar_Ident.text_of_lid
                                                             act1.FStar_Syntax_Syntax.action_name
                                                            in
                                                         let uu____6915 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act1.FStar_Syntax_Syntax.action_defn
                                                            in
                                                         let uu____6917 =
                                                           FStar_Syntax_Print.term_to_string
                                                             act_typ1
                                                            in
                                                         FStar_Util.print3
                                                           "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                           uu____6913
                                                           uu____6915
                                                           uu____6917
                                                       else ());
                                                      (let uu____6922 =
                                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                           env'
                                                           act1.FStar_Syntax_Syntax.action_defn
                                                          in
                                                       match uu____6922 with
                                                       | (act_defn,uu____6930,g_a)
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
                                                           let uu____6934 =
                                                             let act_typ3 =
                                                               FStar_Syntax_Subst.compress
                                                                 act_typ2
                                                                in
                                                             match act_typ3.FStar_Syntax_Syntax.n
                                                             with
                                                             | FStar_Syntax_Syntax.Tm_arrow
                                                                 (bs1,c) ->
                                                                 let uu____6970
                                                                   =
                                                                   FStar_Syntax_Subst.open_comp
                                                                    bs1 c
                                                                    in
                                                                 (match uu____6970
                                                                  with
                                                                  | (bs2,uu____6982)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____6989
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____6989
                                                                     in
                                                                    let uu____6992
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____6992
                                                                    with
                                                                    | 
                                                                    (k1,uu____7006,g)
                                                                    ->
                                                                    (k1, g)))
                                                             | uu____7010 ->
                                                                 let uu____7011
                                                                   =
                                                                   let uu____7017
                                                                    =
                                                                    let uu____7019
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____7021
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7019
                                                                    uu____7021
                                                                     in
                                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7017)
                                                                    in
                                                                 FStar_Errors.raise_error
                                                                   uu____7011
                                                                   act_defn1.FStar_Syntax_Syntax.pos
                                                              in
                                                           (match uu____6934
                                                            with
                                                            | (expected_k,g_k)
                                                                ->
                                                                let g =
                                                                  FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                   in
                                                                ((let uu____7039
                                                                    =
                                                                    let uu____7040
                                                                    =
                                                                    let uu____7041
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7041
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7040
                                                                     in
                                                                  FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____7039);
                                                                 (let act_typ3
                                                                    =
                                                                    let uu____7043
                                                                    =
                                                                    let uu____7044
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____7044.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____7043
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____7069
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____7069
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____7076
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____7076
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____7096
                                                                    =
                                                                    let uu____7097
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____7097]
                                                                     in
                                                                    let uu____7098
                                                                    =
                                                                    let uu____7109
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____7109]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7096;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7098;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____7134
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7134))
                                                                    | 
                                                                    uu____7137
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                  let uu____7139
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____7161
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____7161))
                                                                     in
                                                                  match uu____7139
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
                                                                    let uu___792_7180
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___792_7180.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___792_7180.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___792_7180.FStar_Syntax_Syntax.action_params);
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
                             match uu____5737 with
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
                                   let uu____7205 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length ed_bs)
                                       ed_univs_closing
                                      in
                                   FStar_Syntax_Subst.subst_tscheme
                                     uu____7205 ts1
                                    in
                                 let ed3 =
                                   let uu___804_7215 = ed2  in
                                   let uu____7216 = cl signature  in
                                   let uu____7217 = cl ret_wp  in
                                   let uu____7218 = cl bind_wp  in
                                   let uu____7219 = cl stronger  in
                                   let uu____7220 =
                                     FStar_Syntax_Util.map_match_wps cl
                                       match_wps
                                      in
                                   let uu____7225 =
                                     FStar_Util.map_opt trivial cl  in
                                   let uu____7228 = cl repr  in
                                   let uu____7229 = cl return_repr  in
                                   let uu____7230 = cl bind_repr  in
                                   let uu____7231 =
                                     FStar_List.map
                                       (fun a  ->
                                          let uu___807_7239 = a  in
                                          let uu____7240 =
                                            let uu____7241 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_defn))
                                               in
                                            FStar_All.pipe_right uu____7241
                                              FStar_Pervasives_Native.snd
                                             in
                                          let uu____7266 =
                                            let uu____7267 =
                                              cl
                                                ((a.FStar_Syntax_Syntax.action_univs),
                                                  (a.FStar_Syntax_Syntax.action_typ))
                                               in
                                            FStar_All.pipe_right uu____7267
                                              FStar_Pervasives_Native.snd
                                             in
                                          {
                                            FStar_Syntax_Syntax.action_name =
                                              (uu___807_7239.FStar_Syntax_Syntax.action_name);
                                            FStar_Syntax_Syntax.action_unqualified_name
                                              =
                                              (uu___807_7239.FStar_Syntax_Syntax.action_unqualified_name);
                                            FStar_Syntax_Syntax.action_univs
                                              =
                                              (uu___807_7239.FStar_Syntax_Syntax.action_univs);
                                            FStar_Syntax_Syntax.action_params
                                              =
                                              (uu___807_7239.FStar_Syntax_Syntax.action_params);
                                            FStar_Syntax_Syntax.action_defn =
                                              uu____7240;
                                            FStar_Syntax_Syntax.action_typ =
                                              uu____7266
                                          }) actions
                                      in
                                   {
                                     FStar_Syntax_Syntax.is_layered =
                                       (uu___804_7215.FStar_Syntax_Syntax.is_layered);
                                     FStar_Syntax_Syntax.cattributes =
                                       (uu___804_7215.FStar_Syntax_Syntax.cattributes);
                                     FStar_Syntax_Syntax.mname =
                                       (uu___804_7215.FStar_Syntax_Syntax.mname);
                                     FStar_Syntax_Syntax.univs =
                                       (uu___804_7215.FStar_Syntax_Syntax.univs);
                                     FStar_Syntax_Syntax.binders =
                                       (uu___804_7215.FStar_Syntax_Syntax.binders);
                                     FStar_Syntax_Syntax.signature =
                                       uu____7216;
                                     FStar_Syntax_Syntax.ret_wp = uu____7217;
                                     FStar_Syntax_Syntax.bind_wp = uu____7218;
                                     FStar_Syntax_Syntax.stronger =
                                       uu____7219;
                                     FStar_Syntax_Syntax.match_wps =
                                       uu____7220;
                                     FStar_Syntax_Syntax.trivial = uu____7225;
                                     FStar_Syntax_Syntax.repr = uu____7228;
                                     FStar_Syntax_Syntax.return_repr =
                                       uu____7229;
                                     FStar_Syntax_Syntax.bind_repr =
                                       uu____7230;
                                     FStar_Syntax_Syntax.stronger_repr =
                                       FStar_Pervasives_Native.None;
                                     FStar_Syntax_Syntax.actions = uu____7231;
                                     FStar_Syntax_Syntax.eff_attrs =
                                       (uu___804_7215.FStar_Syntax_Syntax.eff_attrs)
                                   }  in
                                 ((let uu____7293 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env)
                                       (FStar_Options.Other "ED")
                                      in
                                   if uu____7293
                                   then
                                     let uu____7298 =
                                       FStar_Syntax_Print.eff_decl_to_string
                                         false ed3
                                        in
                                     FStar_Util.print1
                                       "Typechecked effect declaration:\n\t%s\n"
                                       uu____7298
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
        let fail1 uu____7363 =
          let uu____7364 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____7370 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____7364 uu____7370  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____7414)::(wp,uu____7416)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____7445 -> fail1 ())
        | uu____7446 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____7459 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____7459
       then
         let uu____7464 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____7464
       else ());
      (let uu____7469 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____7469 with
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
             let uu____7502 =
               ((FStar_Pervasives_Native.fst
                   src_ed.FStar_Syntax_Syntax.is_layered)
                  &&
                  (let uu____7508 =
                     let uu____7509 =
                       FStar_All.pipe_right
                         src_ed.FStar_Syntax_Syntax.is_layered
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____7509 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____7508
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 ((FStar_Pervasives_Native.fst
                     tgt_ed.FStar_Syntax_Syntax.is_layered)
                    &&
                    (let uu____7530 =
                       let uu____7531 =
                         FStar_All.pipe_right
                           tgt_ed.FStar_Syntax_Syntax.is_layered
                           FStar_Pervasives_Native.snd
                          in
                       FStar_All.pipe_right uu____7531 FStar_Util.must  in
                     FStar_Ident.lid_equals uu____7530
                       src_ed.FStar_Syntax_Syntax.mname))
                in
             if uu____7502
             then
               let uu____7549 =
                 let uu____7555 =
                   let uu____7557 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____7560 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____7557 uu____7560
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____7555)  in
               FStar_Errors.raise_error uu____7549 r
             else ());
            (let uu____7567 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____7591 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____7591 with
                  | (us1,lift1) ->
                      let uu____7606 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____7606, us1, lift1))
                in
             match uu____7567 with
             | (env,us1,lift1) ->
                 let uu____7616 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____7616 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____7629 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____7629
                         then
                           let uu____7634 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____7636 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____7634 uu____7636
                         else ());
                        (let lift_t_shape_error s =
                           let uu____7650 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____7652 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____7654 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____7650 uu____7652 s uu____7654
                            in
                         let uu____7657 =
                           let uu____7664 =
                             let uu____7669 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____7669
                               (fun uu____7686  ->
                                  match uu____7686 with
                                  | (t,u) ->
                                      let uu____7697 =
                                        let uu____7698 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____7698
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____7697, u))
                              in
                           match uu____7664 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____7717 =
                                   let uu____7718 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____7718.FStar_Syntax_Syntax.n  in
                                 match uu____7717 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____7730) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____7758 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____7758 with
                                      | (a',uu____7768)::bs1 ->
                                          let uu____7788 =
                                            let uu____7789 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____7789
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____7887 =
                                            let uu____7900 =
                                              let uu____7903 =
                                                let uu____7904 =
                                                  let uu____7911 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____7911)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____7904
                                                 in
                                              [uu____7903]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____7900
                                             in
                                          FStar_All.pipe_right uu____7788
                                            uu____7887)
                                 | uu____7926 ->
                                     let uu____7927 =
                                       let uu____7933 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____7933)
                                        in
                                     FStar_Errors.raise_error uu____7927 r
                                  in
                               let uu____7945 =
                                 let uu____7956 =
                                   let uu____7961 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____7968 =
                                     let uu____7969 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____7969
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____7961 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____7968
                                    in
                                 match uu____7956 with
                                 | (f_sort,g1) ->
                                     let uu____7990 =
                                       let uu____7997 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____7997
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____7990, g1)
                                  in
                               (match uu____7945 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____8064 =
                                      let uu____8069 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____8070 =
                                        let uu____8071 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____8071
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____8069 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____8070
                                       in
                                    (match uu____8064 with
                                     | (repr,g_repr) ->
                                         let uu____8088 =
                                           let uu____8091 =
                                             let uu____8094 =
                                               let uu____8097 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8097
                                                 (fun _8100  ->
                                                    FStar_Pervasives_Native.Some
                                                      _8100)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____8094
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____8091
                                            in
                                         let uu____8101 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____8088, uu____8101)))
                            in
                         match uu____7657 with
                         | (k,g_k) ->
                             ((let uu____8111 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____8111
                               then
                                 let uu____8116 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____8116
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____8125 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____8125
                                then
                                  let uu____8130 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____8130
                                else ());
                               (let uu____8135 =
                                  let uu____8148 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____8148 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____8175 =
                                            let uu____8181 =
                                              let uu____8183 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____8185 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____8187 =
                                                let uu____8189 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____8189
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____8196 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____8183 uu____8185
                                                uu____8187 uu____8196
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____8181)
                                             in
                                          FStar_Errors.raise_error uu____8175
                                            r)
                                       else ();
                                       (let uu____8202 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____8211 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____8211 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____8202
                                        then
                                          let uu____8228 =
                                            let uu____8231 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____8231
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____8228)
                                        else
                                          (let uu____8242 =
                                             let uu____8248 =
                                               let uu____8250 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____8252 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____8254 =
                                                 let uu____8256 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8256
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____8263 =
                                                 let uu____8265 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____8265
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____8272 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____8250 uu____8252
                                                 uu____8254 uu____8263
                                                 uu____8272
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____8248)
                                              in
                                           FStar_Errors.raise_error
                                             uu____8242 r)))
                                   in
                                match uu____8135 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___915_8304 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___915_8304.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___915_8304.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____8314 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____8314
                                      then
                                        let uu____8319 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____8319
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
          (let uu____8351 =
             let uu____8358 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____8358
              in
           match uu____8351 with
           | (a,wp_a_src) ->
               let uu____8365 =
                 let uu____8372 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____8372
                  in
               (match uu____8365 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____8380 =
                        let uu____8383 =
                          let uu____8384 =
                            let uu____8391 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____8391)  in
                          FStar_Syntax_Syntax.NT uu____8384  in
                        [uu____8383]  in
                      FStar_Syntax_Subst.subst uu____8380 wp_b_tgt  in
                    let expected_k =
                      let uu____8399 =
                        let uu____8408 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____8415 =
                          let uu____8424 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____8424]  in
                        uu____8408 :: uu____8415  in
                      let uu____8449 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____8399 uu____8449  in
                    let repr_type eff_name a1 wp =
                      (let uu____8471 =
                         let uu____8473 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____8473  in
                       if uu____8471
                       then
                         let uu____8476 =
                           let uu____8482 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____8482)
                            in
                         let uu____8486 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____8476 uu____8486
                       else ());
                      (let uu____8489 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____8489 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               ed.FStar_Syntax_Syntax.repr
                              in
                           let uu____8522 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____8523 =
                             let uu____8530 =
                               let uu____8531 =
                                 let uu____8548 =
                                   let uu____8559 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____8568 =
                                     let uu____8579 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____8579]  in
                                   uu____8559 :: uu____8568  in
                                 (repr, uu____8548)  in
                               FStar_Syntax_Syntax.Tm_app uu____8531  in
                             FStar_Syntax_Syntax.mk uu____8530  in
                           uu____8523 FStar_Pervasives_Native.None uu____8522)
                       in
                    let uu____8624 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____8797 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____8808 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____8808 with
                              | (usubst,uvs1) ->
                                  let uu____8831 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____8832 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____8831, uu____8832)
                            else (env, lift_wp)  in
                          (match uu____8797 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      tc_check_trivial_guard env1 lift_wp1
                                        expected_k
                                       in
                                    let uu____8882 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____8882))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____8953 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____8968 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____8968 with
                              | (usubst,uvs) ->
                                  let uu____8993 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____8993)
                            else ([], lift)  in
                          (match uu____8953 with
                           | (uvs,lift1) ->
                               ((let uu____9029 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9029
                                 then
                                   let uu____9033 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9033
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9039 =
                                   let uu____9046 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9046 lift1
                                    in
                                 match uu____9039 with
                                 | (lift2,comp,uu____9071) ->
                                     let uu____9072 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____9072 with
                                      | (uu____9101,lift_wp,lift_elab) ->
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
                                            let uu____9133 =
                                              let uu____9144 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____9144
                                               in
                                            let uu____9161 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____9133, uu____9161)
                                          else
                                            (let uu____9190 =
                                               let uu____9201 =
                                                 let uu____9210 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____9210)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____9201
                                                in
                                             let uu____9225 =
                                               let uu____9234 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____9234)  in
                                             (uu____9190, uu____9225))))))
                       in
                    (match uu____8624 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___995_9298 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___995_9298.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___995_9298.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___995_9298.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___995_9298.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___995_9298.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___995_9298.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___995_9298.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___995_9298.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___995_9298.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___995_9298.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___995_9298.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___995_9298.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___995_9298.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___995_9298.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___995_9298.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___995_9298.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___995_9298.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___995_9298.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___995_9298.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___995_9298.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___995_9298.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___995_9298.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___995_9298.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___995_9298.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___995_9298.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___995_9298.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___995_9298.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___995_9298.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___995_9298.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___995_9298.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___995_9298.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___995_9298.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___995_9298.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___995_9298.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___995_9298.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___995_9298.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___995_9298.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___995_9298.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___995_9298.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___995_9298.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___995_9298.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___995_9298.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___995_9298.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___995_9298.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___995_9298.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____9331 =
                                 let uu____9336 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____9336 with
                                 | (usubst,uvs1) ->
                                     let uu____9359 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____9360 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____9359, uu____9360)
                                  in
                               (match uu____9331 with
                                | (env2,lift2) ->
                                    let uu____9365 =
                                      let uu____9372 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____9372
                                       in
                                    (match uu____9365 with
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
                                             let uu____9398 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____9399 =
                                               let uu____9406 =
                                                 let uu____9407 =
                                                   let uu____9424 =
                                                     let uu____9435 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____9444 =
                                                       let uu____9455 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____9455]  in
                                                     uu____9435 :: uu____9444
                                                      in
                                                   (lift_wp1, uu____9424)  in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____9407
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____9406
                                                in
                                             uu____9399
                                               FStar_Pervasives_Native.None
                                               uu____9398
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____9503 =
                                             let uu____9512 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____9519 =
                                               let uu____9528 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____9535 =
                                                 let uu____9544 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____9544]  in
                                               uu____9528 :: uu____9535  in
                                             uu____9512 :: uu____9519  in
                                           let uu____9575 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow uu____9503
                                             uu____9575
                                            in
                                         let uu____9578 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____9578 with
                                          | (expected_k2,uu____9588,uu____9589)
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
                                                   let uu____9597 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____9597))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____9605 =
                             let uu____9607 =
                               let uu____9609 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____9609
                                 FStar_List.length
                                in
                             uu____9607 <> Prims.int_one  in
                           if uu____9605
                           then
                             let uu____9632 =
                               let uu____9638 =
                                 let uu____9640 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9642 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9644 =
                                   let uu____9646 =
                                     let uu____9648 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9648
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9646
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9640 uu____9642 uu____9644
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9638)
                                in
                             FStar_Errors.raise_error uu____9632 r
                           else ());
                          (let uu____9675 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____9678 =
                                  let uu____9680 =
                                    let uu____9683 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____9683
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____9680
                                    FStar_List.length
                                   in
                                uu____9678 <> Prims.int_one)
                              in
                           if uu____9675
                           then
                             let uu____9721 =
                               let uu____9727 =
                                 let uu____9729 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____9731 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____9733 =
                                   let uu____9735 =
                                     let uu____9737 =
                                       let uu____9740 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____9740
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9737
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____9735
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____9729 uu____9731 uu____9733
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____9727)
                                in
                             FStar_Errors.raise_error uu____9721 r
                           else ());
                          (let uu___1032_9782 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1032_9782.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1032_9782.FStar_Syntax_Syntax.target);
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
    fun uu____9813  ->
      fun r  ->
        match uu____9813 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____9836 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____9864 = FStar_Syntax_Subst.univ_var_opening uvs  in
                 match uu____9864 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____9895 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____9895 c  in
                     let uu____9904 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____9904, uvs1, tps1, c1))
               in
            (match uu____9836 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____9924 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____9924 with
                  | (tps2,c2) ->
                      let uu____9939 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____9939 with
                       | (tps3,env3,us) ->
                           let c3 =
                             let uu____9958 =
                               (FStar_Options.use_two_phase_tc ()) &&
                                 (FStar_TypeChecker_Env.should_verify env3)
                                in
                             if uu____9958
                             then
                               let uu____9961 =
                                 FStar_TypeChecker_TcTerm.tc_comp
                                   (let uu___1062_9970 = env3  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___1062_9970.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___1062_9970.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___1062_9970.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___1062_9970.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___1062_9970.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___1062_9970.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___1062_9970.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___1062_9970.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___1062_9970.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___1062_9970.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___1062_9970.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___1062_9970.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___1062_9970.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___1062_9970.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___1062_9970.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___1062_9970.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___1062_9970.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___1062_9970.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___1062_9970.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax = true;
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___1062_9970.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 = true;
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___1062_9970.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___1062_9970.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___1062_9970.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___1062_9970.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___1062_9970.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___1062_9970.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___1062_9970.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___1062_9970.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___1062_9970.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___1062_9970.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___1062_9970.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___1062_9970.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___1062_9970.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___1062_9970.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___1062_9970.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___1062_9970.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___1062_9970.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___1062_9970.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___1062_9970.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___1062_9970.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___1062_9970.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___1062_9970.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___1062_9970.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___1062_9970.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) c2
                                  in
                               match uu____9961 with
                               | (c3,uu____9974,uu____9975) -> c3
                             else c2  in
                           let uu____9978 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c3  in
                           (match uu____9978 with
                            | (c4,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10004)::uu____10005 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10024 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c4  in
                                  let uu____10032 =
                                    let uu____10034 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10034  in
                                  if uu____10032
                                  then
                                    let uu____10037 =
                                      let uu____10043 =
                                        let uu____10045 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10047 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10045 uu____10047
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10043)
                                       in
                                    FStar_Errors.raise_error uu____10037 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c5 =
                                    FStar_Syntax_Subst.close_comp tps4 c4  in
                                  let uu____10055 =
                                    let uu____10056 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c5))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10056
                                     in
                                  match uu____10055 with
                                  | (uvs2,t) ->
                                      let uu____10085 =
                                        let uu____10090 =
                                          let uu____10103 =
                                            let uu____10104 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____10104.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____10103)  in
                                        match uu____10090 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____10119,c6)) -> ([], c6)
                                        | (uu____10161,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c6)) -> (tps5, c6)
                                        | uu____10200 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____10085 with
                                       | (tps5,c6) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____10232 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____10232 with
                                               | (uu____10237,t1) ->
                                                   let uu____10239 =
                                                     let uu____10245 =
                                                       let uu____10247 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____10249 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____10253 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____10247
                                                         uu____10249
                                                         uu____10253
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____10245)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____10239 r)
                                            else ();
                                            (lid, uvs2, tps5, c6)))))))))
  