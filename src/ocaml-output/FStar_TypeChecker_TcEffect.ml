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
            let repr_ts =
              let uu____530 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____530 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____558 = check_and_gen "repr" Prims.int_one repr_ts  in
            match uu____558 with
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
                  let uu____589 =
                    let uu____590 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____590.FStar_Syntax_Syntax.n  in
                  match uu____589 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____593,t,uu____595) ->
                      let uu____620 =
                        let uu____621 = FStar_Syntax_Subst.compress t  in
                        uu____621.FStar_Syntax_Syntax.n  in
                      (match uu____620 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____624,c) ->
                           let uu____646 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____646
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____649 ->
                           let uu____650 =
                             let uu____656 =
                               let uu____658 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____661 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____658 uu____661
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____656)
                              in
                           FStar_Errors.raise_error uu____650 r)
                  | uu____665 ->
                      let uu____666 =
                        let uu____672 =
                          let uu____674 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____677 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____674 uu____677
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____672)  in
                      FStar_Errors.raise_error uu____666 r
                   in
                ((let uu____682 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____688 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____688)
                     in
                  if uu____682
                  then
                    let uu____691 =
                      let uu____697 =
                        let uu____699 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____702 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____699 uu____702
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____697)
                       in
                    FStar_Errors.raise_error uu____691 r
                  else ());
                 (let uu____709 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____709 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____733 = fresh_a_and_u_a "a"  in
                      (match uu____733 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____759 = signature  in
                               match uu____759 with
                               | (us1,t,uu____774) -> (us1, t)  in
                             let uu____791 =
                               let uu____792 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____792
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____791
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____819 =
                               let uu____822 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____822
                                 (fun uu____835  ->
                                    match uu____835 with
                                    | (t,u1) ->
                                        let uu____842 =
                                          let uu____845 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____845
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____842)
                                in
                             FStar_Syntax_Util.arrow bs uu____819  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____848 =
                               let uu____861 =
                                 let uu____864 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____864
                                  in
                               (repr_us, repr_t, uu____861)  in
                             (uu____848, underlying_effect_lid))))))
             in
          match uu____508 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____937 = signature  in
                    match uu____937 with | (us,t,uu____952) -> (us, t)  in
                  let uu____969 =
                    FStar_TypeChecker_Env.inst_tscheme_with signature_ts [u]
                     in
                  match uu____969 with
                  | (uu____978,signature1) ->
                      let repr_ts =
                        let uu____981 = repr  in
                        match uu____981 with | (us,t,uu____996) -> (us, t)
                         in
                      FStar_TypeChecker_Util.fresh_effect_repr env r
                        ed.FStar_Syntax_Syntax.mname signature1
                        (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1046 =
                    let uu____1052 =
                      let uu____1054 = FStar_Util.string_of_int n1  in
                      let uu____1056 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1058 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1054 uu____1056 uu____1058
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1052)  in
                  FStar_Errors.raise_error uu____1046 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1088 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1088 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1116 =
                    check_and_gen "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1116 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1140 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1140 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1160 = fresh_a_and_u_a "a"  in
                           (match uu____1160 with
                            | (a,u_a) ->
                                let rest_bs =
                                  let uu____1189 =
                                    let uu____1190 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1190.FStar_Syntax_Syntax.n  in
                                  match uu____1189 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1202) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1230 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1230 with
                                       | (a',uu____1240)::bs1 ->
                                           let uu____1260 =
                                             let uu____1261 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - Prims.int_one))
                                                in
                                             FStar_All.pipe_right uu____1261
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____1359 =
                                             let uu____1372 =
                                               let uu____1375 =
                                                 let uu____1376 =
                                                   let uu____1383 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a)
                                                      in
                                                   (a', uu____1383)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1376
                                                  in
                                               [uu____1375]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1372
                                              in
                                           FStar_All.pipe_right uu____1260
                                             uu____1359)
                                  | uu____1398 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs =
                                  let uu____1410 =
                                    let uu____1419 =
                                      let uu____1428 = fresh_x_a "x" a  in
                                      [uu____1428]  in
                                    FStar_List.append rest_bs uu____1419  in
                                  a :: uu____1410  in
                                let uu____1460 =
                                  let uu____1465 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1466 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1465 u_a uu____1466  in
                                (match uu____1460 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1486 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1486
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1491 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1491);
                                      (let uu____1492 =
                                         let uu____1495 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1495
                                          in
                                       (ret_us, ret_t, uu____1492))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1522 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1522 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1534 =
                     check_and_gen "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1534 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1558 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1558 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1578 = fresh_a_and_u_a "a"  in
                            (match uu____1578 with
                             | (a,u_a) ->
                                 let uu____1598 = fresh_a_and_u_a "b"  in
                                 (match uu____1598 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1627 =
                                          let uu____1628 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1628.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1627 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1640) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1668 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1668 with
                                             | (a',uu____1678)::(b',uu____1680)::bs1
                                                 ->
                                                 let uu____1710 =
                                                   let uu____1711 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1711
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1809 =
                                                   let uu____1822 =
                                                     let uu____1825 =
                                                       let uu____1826 =
                                                         let uu____1833 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1833)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1826
                                                        in
                                                     let uu____1840 =
                                                       let uu____1843 =
                                                         let uu____1844 =
                                                           let uu____1851 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1851)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1844
                                                          in
                                                       [uu____1843]  in
                                                     uu____1825 :: uu____1840
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1822
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1710 uu____1809)
                                        | uu____1866 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1890 =
                                        let uu____1901 =
                                          let uu____1906 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1907 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1906 u_a
                                            uu____1907
                                           in
                                        match uu____1901 with
                                        | (repr1,g) ->
                                            let uu____1922 =
                                              let uu____1929 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1929
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1922, g)
                                         in
                                      (match uu____1890 with
                                       | (f,guard_f) ->
                                           let uu____1969 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1982 =
                                               let uu____1987 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____2006 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1987 u_b
                                                 uu____2006
                                                in
                                             match uu____1982 with
                                             | (repr1,g) ->
                                                 let uu____2021 =
                                                   let uu____2028 =
                                                     let uu____2029 =
                                                       let uu____2030 =
                                                         let uu____2033 =
                                                           let uu____2036 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____2036
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____2033
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____2030
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____2029
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2028
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____2021, g)
                                              in
                                           (match uu____1969 with
                                            | (g,guard_g) ->
                                                let uu____2088 =
                                                  let uu____2093 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2094 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2093 u_b
                                                    uu____2094
                                                   in
                                                (match uu____2088 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2114 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2114
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
                                                      (let uu____2143 =
                                                         let uu____2146 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2146
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2143)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2173 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2173 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2201 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2201 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2226 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2226
                          then
                            let uu____2231 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2237 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2231 uu____2237
                          else ());
                         (let uu____2246 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2246 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2266 = fresh_a_and_u_a "a"  in
                              (match uu____2266 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2295 =
                                       let uu____2296 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2296.FStar_Syntax_Syntax.n  in
                                     match uu____2295 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2308) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2336 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2336 with
                                          | (a',uu____2346)::bs1 ->
                                              let uu____2366 =
                                                let uu____2367 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2367
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2465 =
                                                let uu____2478 =
                                                  let uu____2481 =
                                                    let uu____2482 =
                                                      let uu____2489 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2489)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2482
                                                     in
                                                  [uu____2481]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2478
                                                 in
                                              FStar_All.pipe_right uu____2366
                                                uu____2465)
                                     | uu____2504 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2522 =
                                     let uu____2533 =
                                       let uu____2538 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2539 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2538 u uu____2539
                                        in
                                     match uu____2533 with
                                     | (repr1,g) ->
                                         let uu____2554 =
                                           let uu____2561 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2561
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2554, g)
                                      in
                                   (match uu____2522 with
                                    | (f,guard_f) ->
                                        let uu____2601 =
                                          let uu____2606 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2607 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2606 u
                                            uu____2607
                                           in
                                        (match uu____2601 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2626 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2626 FStar_Util.must
                                                  in
                                               let uu____2631 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2631 with
                                               | (uu____2636,pure_wp_t) ->
                                                   let uu____2638 =
                                                     let uu____2643 =
                                                       let uu____2644 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2644]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2643
                                                      in
                                                   uu____2638
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2677 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2693 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2693
                                                 pure_wp_t
                                                in
                                             (match uu____2677 with
                                              | (pure_wp_uvar,uu____2707,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2722 =
                                                      let uu____2723 =
                                                        let uu____2724 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2724]  in
                                                      let uu____2725 =
                                                        let uu____2736 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2736]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2723;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2725;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2722
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2791 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2791
                                                    then
                                                      let uu____2796 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2796
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
                                                     let uu____2804 =
                                                       let uu____2807 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2807
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2804))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2836 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2836 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2864 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2864 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2888 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2888 with
                          | (us,t) ->
                              let uu____2907 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2907 with
                               | (uu____2924,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2927 = fresh_a_and_u_a "a"  in
                                   (match uu____2927 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2956 =
                                            let uu____2957 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2957.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2956 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2969) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2997 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2997 with
                                               | (a',uu____3007)::bs1 ->
                                                   let uu____3027 =
                                                     let uu____3028 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3028
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3126 =
                                                     let uu____3139 =
                                                       let uu____3142 =
                                                         let uu____3143 =
                                                           let uu____3150 =
                                                             let uu____3153 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3153
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3150)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3143
                                                          in
                                                       [uu____3142]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3139
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3027 uu____3126)
                                          | uu____3174 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3192 =
                                          let uu____3203 =
                                            let uu____3208 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3209 =
                                              let uu____3210 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3210
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3208 u_a
                                              uu____3209
                                             in
                                          match uu____3203 with
                                          | (repr1,g) ->
                                              let uu____3231 =
                                                let uu____3238 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3238
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3231, g)
                                           in
                                        (match uu____3192 with
                                         | (f_bs,guard_f) ->
                                             let uu____3278 =
                                               let uu____3289 =
                                                 let uu____3294 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3295 =
                                                   let uu____3296 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3296
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3294 u_a
                                                   uu____3295
                                                  in
                                               match uu____3289 with
                                               | (repr1,g) ->
                                                   let uu____3317 =
                                                     let uu____3324 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3324
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3317, g)
                                                in
                                             (match uu____3278 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3371 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3371
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3379 =
                                                    let uu____3384 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3403 =
                                                      let uu____3404 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3404
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3384
                                                      u_a uu____3403
                                                     in
                                                  (match uu____3379 with
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
                                                        (let uu____3464 =
                                                           let uu____3467 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3467
                                                            in
                                                         (if_then_else_us,
                                                           uu____3464,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3478 =
                        let uu____3481 =
                          let uu____3490 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3490 FStar_Util.must  in
                        FStar_All.pipe_right uu____3481
                          FStar_Pervasives_Native.snd
                         in
                      uu____3478.FStar_Syntax_Syntax.pos  in
                    let uu____3519 = if_then_else1  in
                    match uu____3519 with
                    | (ite_us,ite_t,uu____3534) ->
                        let uu____3547 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3547 with
                         | (us,ite_t1) ->
                             let uu____3554 =
                               let uu____3565 =
                                 let uu____3566 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3566.FStar_Syntax_Syntax.n  in
                               match uu____3565 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3580,uu____3581) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3607 =
                                     let uu____3614 =
                                       let uu____3617 =
                                         let uu____3620 =
                                           let uu____3629 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3629
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3620
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3617
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3614
                                       (fun l  ->
                                          let uu____3773 = l  in
                                          match uu____3773 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3607 with
                                    | (f,g,p) ->
                                        let uu____3798 =
                                          let uu____3799 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3799 bs1
                                           in
                                        let uu____3800 =
                                          let uu____3801 =
                                            let uu____3806 =
                                              let uu____3807 =
                                                let uu____3810 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3810
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3807
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3806
                                             in
                                          uu____3801
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3798, uu____3800, f, g, p))
                               | uu____3837 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3554 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3854 =
                                    let uu____3863 = stronger_repr  in
                                    match uu____3863 with
                                    | (uu____3884,subcomp_t,subcomp_ty) ->
                                        let uu____3899 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3899 with
                                         | (uu____3912,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3923 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3923 with
                                               | (uu____3936,subcomp_ty1) ->
                                                   let uu____3938 =
                                                     let uu____3939 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3939.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3938 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3951) ->
                                                        let uu____3972 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3972
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4078 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4096 =
                                                 let uu____4101 =
                                                   let uu____4102 =
                                                     let uu____4105 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4125 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4105 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4102
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4101
                                                  in
                                               uu____4096
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4134 = aux f_t  in
                                             let uu____4137 = aux g_t  in
                                             (uu____4134, uu____4137))
                                     in
                                  (match uu____3854 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4154 =
                                         let aux t =
                                           let uu____4171 =
                                             let uu____4178 =
                                               let uu____4179 =
                                                 let uu____4206 =
                                                   let uu____4223 =
                                                     let uu____4232 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4232
                                                      in
                                                   (uu____4223,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4206,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4179
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4178
                                              in
                                           uu____4171
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4273 = aux subcomp_f  in
                                         let uu____4274 = aux subcomp_g  in
                                         (uu____4273, uu____4274)  in
                                       (match uu____4154 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4278 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4278
                                              then
                                                let uu____4283 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4285 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4283 uu____4285
                                              else ());
                                             (let uu____4290 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4290 with
                                              | (uu____4297,uu____4298,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4301 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4301 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4303 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4303 with
                                                    | (uu____4310,uu____4311,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4317 =
                                                              let uu____4322
                                                                =
                                                                let uu____4323
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4323
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4324
                                                                =
                                                                let uu____4325
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4325]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4322
                                                                uu____4324
                                                               in
                                                            uu____4317
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4358 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4358 g_g
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
                        (let uu____4382 =
                           let uu____4388 =
                             let uu____4390 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4390
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4388)
                            in
                         FStar_Errors.raise_error uu____4382 r)
                      else ();
                      (let uu____4397 =
                         let uu____4402 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4402 with
                         | (usubst,us) ->
                             let uu____4425 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4426 =
                               let uu___416_4427 = act  in
                               let uu____4428 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4429 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___416_4427.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___416_4427.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___416_4427.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4428;
                                 FStar_Syntax_Syntax.action_typ = uu____4429
                               }  in
                             (uu____4425, uu____4426)
                          in
                       match uu____4397 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4433 =
                               let uu____4434 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4434.FStar_Syntax_Syntax.n  in
                             match uu____4433 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4460 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4460
                                 then
                                   let repr_ts =
                                     let uu____4464 = repr  in
                                     match uu____4464 with
                                     | (us,t,uu____4479) -> (us, t)  in
                                   let repr1 =
                                     let uu____4497 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4497
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4509 =
                                       let uu____4514 =
                                         let uu____4515 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4515 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4514
                                        in
                                     uu____4509 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4533 =
                                       let uu____4536 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4536
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4533
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4539 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4540 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4540 with
                            | (act_typ1,uu____4548,g_t) ->
                                let uu____4550 =
                                  let uu____4557 =
                                    let uu___441_4558 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___441_4558.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___441_4558.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___441_4558.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___441_4558.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___441_4558.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___441_4558.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___441_4558.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___441_4558.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___441_4558.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___441_4558.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___441_4558.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___441_4558.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___441_4558.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___441_4558.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___441_4558.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___441_4558.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___441_4558.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___441_4558.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___441_4558.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___441_4558.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___441_4558.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___441_4558.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___441_4558.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___441_4558.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___441_4558.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___441_4558.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___441_4558.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___441_4558.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___441_4558.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___441_4558.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___441_4558.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___441_4558.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___441_4558.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___441_4558.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___441_4558.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___441_4558.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___441_4558.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___441_4558.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___441_4558.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___441_4558.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___441_4558.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___441_4558.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___441_4558.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___441_4558.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4557
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4550 with
                                 | (act_defn,uu____4561,g_d) ->
                                     ((let uu____4564 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4564
                                       then
                                         let uu____4569 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4571 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4569 uu____4571
                                       else ());
                                      (let uu____4576 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4584 =
                                           let uu____4585 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4585.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4584 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4595) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4618 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4618 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4634 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4634 with
                                                   | (a_tm,uu____4654,g_tm)
                                                       ->
                                                       let uu____4668 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4668 with
                                                        | (repr1,g) ->
                                                            let uu____4681 =
                                                              let uu____4684
                                                                =
                                                                let uu____4687
                                                                  =
                                                                  let uu____4690
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4690
                                                                    (
                                                                    fun _4693
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4693)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4687
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4684
                                                               in
                                                            let uu____4694 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4681,
                                                              uu____4694))))
                                         | uu____4697 ->
                                             let uu____4698 =
                                               let uu____4704 =
                                                 let uu____4706 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4706
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4704)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4698 r
                                          in
                                       match uu____4576 with
                                       | (k,g_k) ->
                                           ((let uu____4723 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4723
                                             then
                                               let uu____4728 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4728
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4736 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4736
                                              then
                                                let uu____4741 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4741
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4754 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4754
                                                   in
                                                let repr_args t =
                                                  let uu____4775 =
                                                    let uu____4776 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4776.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4775 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4828 =
                                                        let uu____4829 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4829.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4828 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4838,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4848 ->
                                                           let uu____4849 =
                                                             let uu____4855 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4855)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4849 r)
                                                  | uu____4864 ->
                                                      let uu____4865 =
                                                        let uu____4871 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4871)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4865 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4881 =
                                                  let uu____4882 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4882.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4881 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4907 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4907 with
                                                     | (bs1,c1) ->
                                                         let uu____4914 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4914
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
                                                              let uu____4925
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4925))
                                                | uu____4928 ->
                                                    let uu____4929 =
                                                      let uu____4935 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4935)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4929 r
                                                 in
                                              (let uu____4939 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4939
                                               then
                                                 let uu____4944 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4944
                                               else ());
                                              (let act2 =
                                                 let uu____4950 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4950 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___514_4964 =
                                                         act1  in
                                                       let uu____4965 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___514_4964.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___514_4964.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___514_4964.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4965
                                                       }
                                                     else
                                                       (let uu____4968 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4975
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4975
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4968
                                                        then
                                                          let uu___519_4980 =
                                                            act1  in
                                                          let uu____4981 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___519_4980.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___519_4980.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___519_4980.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___519_4980.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4981
                                                          }
                                                        else
                                                          (let uu____4984 =
                                                             let uu____4990 =
                                                               let uu____4992
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4994
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4992
                                                                 uu____4994
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4990)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4984 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5019 =
                      match uu____5019 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5064 =
                        let uu____5065 = tschemes_of repr  in
                        let uu____5070 = tschemes_of return_repr  in
                        let uu____5075 = tschemes_of bind_repr  in
                        let uu____5080 = tschemes_of stronger_repr  in
                        let uu____5085 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5065;
                          FStar_Syntax_Syntax.l_return = uu____5070;
                          FStar_Syntax_Syntax.l_bind = uu____5075;
                          FStar_Syntax_Syntax.l_subcomp = uu____5080;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5085
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5064  in
                    let uu___528_5090 = ed  in
                    let uu____5091 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___528_5090.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___528_5090.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___528_5090.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___528_5090.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5098 = signature  in
                         match uu____5098 with | (us,t,uu____5113) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5091;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___528_5090.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5146 =
          FStar_TypeChecker_TcTerm.tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5146
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5168 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5168
         then
           let uu____5173 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5173
         else ());
        (let uu____5179 =
           let uu____5184 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5184 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5208 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5208  in
               let uu____5209 =
                 let uu____5216 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5216 bs  in
               (match uu____5209 with
                | (bs1,uu____5222,uu____5223) ->
                    let uu____5224 =
                      let tmp_t =
                        let uu____5234 =
                          let uu____5237 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5242  ->
                                 FStar_Pervasives_Native.Some _5242)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5237
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5234  in
                      let uu____5243 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5243 with
                      | (us,tmp_t1) ->
                          let uu____5260 =
                            let uu____5261 =
                              let uu____5262 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5262
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5261
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5260)
                       in
                    (match uu____5224 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5299 ->
                              let uu____5302 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5309 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5309 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5302
                              then (us, bs2)
                              else
                                (let uu____5320 =
                                   let uu____5326 =
                                     let uu____5328 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5330 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5328 uu____5330
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5326)
                                    in
                                 let uu____5334 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5320
                                   uu____5334))))
            in
         match uu____5179 with
         | (us,bs) ->
             let ed1 =
               let uu___565_5342 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___565_5342.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___565_5342.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___565_5342.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___565_5342.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___565_5342.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___565_5342.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5343 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5343 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5362 =
                    let uu____5367 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5367  in
                  (match uu____5362 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5388 =
                           match uu____5388 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5408 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5408 t  in
                               let uu____5417 =
                                 let uu____5418 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5418 t1  in
                               (us1, uu____5417)
                            in
                         let uu___579_5423 = ed1  in
                         let uu____5424 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5425 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5426 =
                           FStar_List.map
                             (fun a  ->
                                let uu___582_5434 = a  in
                                let uu____5435 =
                                  let uu____5436 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5436  in
                                let uu____5447 =
                                  let uu____5448 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5448  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___582_5434.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___582_5434.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___582_5434.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___582_5434.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5435;
                                  FStar_Syntax_Syntax.action_typ = uu____5447
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___579_5423.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___579_5423.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___579_5423.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___579_5423.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5424;
                           FStar_Syntax_Syntax.combinators = uu____5425;
                           FStar_Syntax_Syntax.actions = uu____5426;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___579_5423.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5460 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5460
                         then
                           let uu____5465 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5465
                         else ());
                        (let env =
                           let uu____5472 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5472
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5507 k =
                           match uu____5507 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5527 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5527 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5536 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5536 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5537 =
                                            let uu____5544 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5544 t1
                                             in
                                          (match uu____5537 with
                                           | (t2,uu____5546,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5549 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5549 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5565 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5567 =
                                                 let uu____5569 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5569
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5565 uu____5567
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5584 ->
                                               let uu____5585 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5592 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5592 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5585
                                               then (g_us, t3)
                                               else
                                                 (let uu____5603 =
                                                    let uu____5609 =
                                                      let uu____5611 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5613 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5611
                                                        uu____5613
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5609)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5603
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5621 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5621
                          then
                            let uu____5626 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5626
                          else ());
                         (let fresh_a_and_wp uu____5642 =
                            let fail1 t =
                              let uu____5655 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5655
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5671 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5671 with
                            | (uu____5682,signature1) ->
                                let uu____5684 =
                                  let uu____5685 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5685.FStar_Syntax_Syntax.n  in
                                (match uu____5684 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5695) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5724)::(wp,uu____5726)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5755 -> fail1 signature1)
                                 | uu____5756 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5770 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5770
                            then
                              let uu____5775 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5775
                            else ()  in
                          let ret_wp =
                            let uu____5781 = fresh_a_and_wp ()  in
                            match uu____5781 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5797 =
                                    let uu____5806 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5813 =
                                      let uu____5822 =
                                        let uu____5829 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5829
                                         in
                                      [uu____5822]  in
                                    uu____5806 :: uu____5813  in
                                  let uu____5848 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5797
                                    uu____5848
                                   in
                                let uu____5851 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5851
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5865 = fresh_a_and_wp ()  in
                             match uu____5865 with
                             | (a,wp_sort_a) ->
                                 let uu____5878 = fresh_a_and_wp ()  in
                                 (match uu____5878 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5894 =
                                          let uu____5903 =
                                            let uu____5910 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5910
                                             in
                                          [uu____5903]  in
                                        let uu____5923 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5894
                                          uu____5923
                                         in
                                      let k =
                                        let uu____5929 =
                                          let uu____5938 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5945 =
                                            let uu____5954 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5961 =
                                              let uu____5970 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5977 =
                                                let uu____5986 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5993 =
                                                  let uu____6002 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6002]  in
                                                uu____5986 :: uu____5993  in
                                              uu____5970 :: uu____5977  in
                                            uu____5954 :: uu____5961  in
                                          uu____5938 :: uu____5945  in
                                        let uu____6045 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5929
                                          uu____6045
                                         in
                                      let uu____6048 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6048
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6062 = fresh_a_and_wp ()  in
                              match uu____6062 with
                              | (a,wp_sort_a) ->
                                  let uu____6075 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6075 with
                                   | (t,uu____6081) ->
                                       let k =
                                         let uu____6085 =
                                           let uu____6094 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6101 =
                                             let uu____6110 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6117 =
                                               let uu____6126 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6126]  in
                                             uu____6110 :: uu____6117  in
                                           uu____6094 :: uu____6101  in
                                         let uu____6157 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6085
                                           uu____6157
                                          in
                                       let uu____6160 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6160
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6174 = fresh_a_and_wp ()  in
                               match uu____6174 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6188 =
                                       let uu____6191 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6191
                                        in
                                     let uu____6192 =
                                       let uu____6193 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6193
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6188
                                       uu____6192
                                      in
                                   let k =
                                     let uu____6205 =
                                       let uu____6214 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6221 =
                                         let uu____6230 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6237 =
                                           let uu____6246 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6253 =
                                             let uu____6262 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6262]  in
                                           uu____6246 :: uu____6253  in
                                         uu____6230 :: uu____6237  in
                                       uu____6214 :: uu____6221  in
                                     let uu____6299 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6205
                                       uu____6299
                                      in
                                   let uu____6302 =
                                     let uu____6307 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6307
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6302
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6339 = fresh_a_and_wp ()  in
                                match uu____6339 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6355 =
                                        let uu____6364 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6371 =
                                          let uu____6380 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6380]  in
                                        uu____6364 :: uu____6371  in
                                      let uu____6405 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6355
                                        uu____6405
                                       in
                                    let uu____6408 =
                                      let uu____6413 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6413
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6408
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6429 = fresh_a_and_wp ()  in
                                 match uu____6429 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6443 =
                                         let uu____6446 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6446
                                          in
                                       let uu____6447 =
                                         let uu____6448 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6448
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6443
                                         uu____6447
                                        in
                                     let wp_sort_b_a =
                                       let uu____6460 =
                                         let uu____6469 =
                                           let uu____6476 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6476
                                            in
                                         [uu____6469]  in
                                       let uu____6489 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6460
                                         uu____6489
                                        in
                                     let k =
                                       let uu____6495 =
                                         let uu____6504 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6511 =
                                           let uu____6520 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6527 =
                                             let uu____6536 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6536]  in
                                           uu____6520 :: uu____6527  in
                                         uu____6504 :: uu____6511  in
                                       let uu____6567 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6495
                                         uu____6567
                                        in
                                     let uu____6570 =
                                       let uu____6575 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6575
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6570
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6591 = fresh_a_and_wp ()  in
                                  match uu____6591 with
                                  | (a,wp_sort_a) ->
                                      let uu____6604 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6604 with
                                       | (t,uu____6610) ->
                                           let k =
                                             let uu____6614 =
                                               let uu____6623 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6630 =
                                                 let uu____6639 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6639]  in
                                               uu____6623 :: uu____6630  in
                                             let uu____6664 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6614 uu____6664
                                              in
                                           let trivial =
                                             let uu____6668 =
                                               let uu____6673 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6673 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6668
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6688 =
                                  let uu____6705 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6705 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6734 ->
                                      let repr =
                                        let uu____6738 = fresh_a_and_wp ()
                                           in
                                        match uu____6738 with
                                        | (a,wp_sort_a) ->
                                            let uu____6751 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6751 with
                                             | (t,uu____6757) ->
                                                 let k =
                                                   let uu____6761 =
                                                     let uu____6770 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6777 =
                                                       let uu____6786 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6786]  in
                                                     uu____6770 :: uu____6777
                                                      in
                                                   let uu____6811 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6761 uu____6811
                                                    in
                                                 let uu____6814 =
                                                   let uu____6819 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6819
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6814
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6863 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6863 with
                                          | (uu____6870,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6873 =
                                                let uu____6880 =
                                                  let uu____6881 =
                                                    let uu____6898 =
                                                      let uu____6909 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6926 =
                                                        let uu____6937 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6937]  in
                                                      uu____6909 ::
                                                        uu____6926
                                                       in
                                                    (repr2, uu____6898)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6881
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6880
                                                 in
                                              uu____6873
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7003 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7003 wp  in
                                        let destruct_repr t =
                                          let uu____7018 =
                                            let uu____7019 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7019.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7018 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7030,(t1,uu____7032)::
                                               (wp,uu____7034)::[])
                                              -> (t1, wp)
                                          | uu____7093 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7109 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7109
                                              FStar_Util.must
                                             in
                                          let uu____7136 = fresh_a_and_wp ()
                                             in
                                          match uu____7136 with
                                          | (a,uu____7144) ->
                                              let x_a =
                                                let uu____7150 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7150
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7158 =
                                                    let uu____7163 =
                                                      let uu____7164 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7164
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7173 =
                                                      let uu____7174 =
                                                        let uu____7183 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7183
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7192 =
                                                        let uu____7203 =
                                                          let uu____7212 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7212
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7203]  in
                                                      uu____7174 ::
                                                        uu____7192
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7163 uu____7173
                                                     in
                                                  uu____7158
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7248 =
                                                  let uu____7257 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7264 =
                                                    let uu____7273 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7273]  in
                                                  uu____7257 :: uu____7264
                                                   in
                                                let uu____7298 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7248 uu____7298
                                                 in
                                              let uu____7301 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7301 with
                                               | (k1,uu____7309,uu____7310)
                                                   ->
                                                   let env1 =
                                                     let uu____7314 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7314
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
                                             let uu____7327 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7327
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7365 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7365
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7366 = fresh_a_and_wp ()
                                              in
                                           match uu____7366 with
                                           | (a,wp_sort_a) ->
                                               let uu____7379 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7379 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7395 =
                                                        let uu____7404 =
                                                          let uu____7411 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7411
                                                           in
                                                        [uu____7404]  in
                                                      let uu____7424 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7395 uu____7424
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
                                                      let uu____7432 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7432
                                                       in
                                                    let wp_g_x =
                                                      let uu____7437 =
                                                        let uu____7442 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7443 =
                                                          let uu____7444 =
                                                            let uu____7453 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7453
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7444]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7442
                                                          uu____7443
                                                         in
                                                      uu____7437
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7484 =
                                                          let uu____7489 =
                                                            let uu____7490 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7490
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7499 =
                                                            let uu____7500 =
                                                              let uu____7503
                                                                =
                                                                let uu____7506
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7507
                                                                  =
                                                                  let uu____7510
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7511
                                                                    =
                                                                    let uu____7514
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7515
                                                                    =
                                                                    let uu____7518
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7518]
                                                                     in
                                                                    uu____7514
                                                                    ::
                                                                    uu____7515
                                                                     in
                                                                  uu____7510
                                                                    ::
                                                                    uu____7511
                                                                   in
                                                                uu____7506 ::
                                                                  uu____7507
                                                                 in
                                                              r :: uu____7503
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7500
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7489
                                                            uu____7499
                                                           in
                                                        uu____7484
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7536 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7536
                                                      then
                                                        let uu____7547 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7554 =
                                                          let uu____7563 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7563]  in
                                                        uu____7547 ::
                                                          uu____7554
                                                      else []  in
                                                    let k =
                                                      let uu____7599 =
                                                        let uu____7608 =
                                                          let uu____7617 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7624 =
                                                            let uu____7633 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7633]  in
                                                          uu____7617 ::
                                                            uu____7624
                                                           in
                                                        let uu____7658 =
                                                          let uu____7667 =
                                                            let uu____7676 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7683 =
                                                              let uu____7692
                                                                =
                                                                let uu____7699
                                                                  =
                                                                  let uu____7700
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7700
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7699
                                                                 in
                                                              let uu____7701
                                                                =
                                                                let uu____7710
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7717
                                                                  =
                                                                  let uu____7726
                                                                    =
                                                                    let uu____7733
                                                                    =
                                                                    let uu____7734
                                                                    =
                                                                    let uu____7743
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7743]
                                                                     in
                                                                    let uu____7762
                                                                    =
                                                                    let uu____7765
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7765
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7734
                                                                    uu____7762
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7733
                                                                     in
                                                                  [uu____7726]
                                                                   in
                                                                uu____7710 ::
                                                                  uu____7717
                                                                 in
                                                              uu____7692 ::
                                                                uu____7701
                                                               in
                                                            uu____7676 ::
                                                              uu____7683
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7667
                                                           in
                                                        FStar_List.append
                                                          uu____7608
                                                          uu____7658
                                                         in
                                                      let uu____7810 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7599 uu____7810
                                                       in
                                                    let uu____7813 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7813 with
                                                     | (k1,uu____7821,uu____7822)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___777_7832
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___777_7832.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7834  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7834)
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
                                              (let uu____7861 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7875 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7875 with
                                                    | (usubst,uvs) ->
                                                        let uu____7898 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7899 =
                                                          let uu___790_7900 =
                                                            act  in
                                                          let uu____7901 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7902 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___790_7900.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___790_7900.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___790_7900.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7901;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7902
                                                          }  in
                                                        (uu____7898,
                                                          uu____7899))
                                                  in
                                               match uu____7861 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7906 =
                                                       let uu____7907 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7907.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7906 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7933 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7933
                                                         then
                                                           let uu____7936 =
                                                             let uu____7939 =
                                                               let uu____7940
                                                                 =
                                                                 let uu____7941
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7941
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7940
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7939
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7936
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7964 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7965 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7965 with
                                                    | (act_typ1,uu____7973,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___807_7976 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___807_7976.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7979 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7979
                                                          then
                                                            let uu____7983 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7985 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7987 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7983
                                                              uu____7985
                                                              uu____7987
                                                          else ());
                                                         (let uu____7992 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7992
                                                          with
                                                          | (act_defn,uu____8000,g_a)
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
                                                              let uu____8004
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
                                                                    let uu____8040
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8040
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8052)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8059
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8059
                                                                     in
                                                                    let uu____8062
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8062
                                                                    with
                                                                    | 
                                                                    (k1,uu____8076,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8080
                                                                    ->
                                                                    let uu____8081
                                                                    =
                                                                    let uu____8087
                                                                    =
                                                                    let uu____8089
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8091
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8089
                                                                    uu____8091
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8087)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8081
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8004
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
                                                                    let uu____8109
                                                                    =
                                                                    let uu____8110
                                                                    =
                                                                    let uu____8111
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8111
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8110
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8109);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8113
                                                                    =
                                                                    let uu____8114
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8114.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8113
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8139
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8139
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8146
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8146
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8166
                                                                    =
                                                                    let uu____8167
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8167]
                                                                     in
                                                                    let uu____8168
                                                                    =
                                                                    let uu____8179
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8179]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8166;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8168;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8204
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8204))
                                                                    | 
                                                                    uu____8207
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8209
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8231
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8231))
                                                                     in
                                                                    match uu____8209
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
                                                                    let uu___857_8250
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___857_8250.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___857_8250.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___857_8250.FStar_Syntax_Syntax.action_params);
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
                                match uu____6688 with
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
                                      let uu____8293 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8293 ts1
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
                                          uu____8305 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8306 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8307 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___877_8310 = ed2  in
                                      let uu____8311 = cl signature  in
                                      let uu____8312 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___880_8320 = a  in
                                             let uu____8321 =
                                               let uu____8322 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8322
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8347 =
                                               let uu____8348 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8348
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___880_8320.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___880_8320.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___880_8320.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___880_8320.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8321;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8347
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___877_8310.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___877_8310.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___877_8310.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___877_8310.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8311;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8312;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___877_8310.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8374 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8374
                                      then
                                        let uu____8379 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8379
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
        let uu____8405 =
          let uu____8420 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8420 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8405 env ed quals
  
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
        let fail1 uu____8470 =
          let uu____8471 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8477 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8471 uu____8477  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8521)::(wp,uu____8523)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8552 -> fail1 ())
        | uu____8553 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8566 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8566
       then
         let uu____8571 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8571
       else ());
      (let uu____8576 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift_wp
           FStar_Util.must
          in
       match uu____8576 with
       | (us,lift) ->
           let r = lift.FStar_Syntax_Syntax.pos  in
           ((let src_ed =
               let uu____8624 =
                 FStar_All.pipe_right sub1.FStar_Syntax_Syntax.source
                   (FStar_TypeChecker_Env.norm_eff_name env0)
                  in
               FStar_All.pipe_right uu____8624
                 (FStar_TypeChecker_Env.get_effect_decl env0)
                in
             let tgt_ed =
               FStar_TypeChecker_Env.get_effect_decl env0
                 sub1.FStar_Syntax_Syntax.target
                in
             let uu____8626 =
               ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
                  (let uu____8630 =
                     let uu____8631 =
                       FStar_All.pipe_right src_ed
                         FStar_Syntax_Util.get_layered_effect_base
                        in
                     FStar_All.pipe_right uu____8631 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8630
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered)
                     &&
                     (let uu____8640 =
                        let uu____8641 =
                          FStar_All.pipe_right tgt_ed
                            FStar_Syntax_Util.get_layered_effect_base
                           in
                        FStar_All.pipe_right uu____8641 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8640
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8649 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8649))
                in
             if uu____8626
             then
               let uu____8652 =
                 let uu____8658 =
                   let uu____8660 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8663 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8660 uu____8663
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8658)  in
               FStar_Errors.raise_error uu____8652 r
             else ());
            (let uu____8670 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8694 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8694 with
                  | (us1,lift1) ->
                      let uu____8709 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8709, us1, lift1))
                in
             match uu____8670 with
             | (env,us1,lift1) ->
                 let uu____8719 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8719 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8732 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8732
                         then
                           let uu____8737 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8739 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8737 uu____8739
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8753 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8755 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8757 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8753 uu____8755 s uu____8757
                            in
                         let uu____8760 =
                           let uu____8767 =
                             let uu____8772 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8772
                               (fun uu____8789  ->
                                  match uu____8789 with
                                  | (t,u) ->
                                      let uu____8800 =
                                        let uu____8801 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8801
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8800, u))
                              in
                           match uu____8767 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8820 =
                                   let uu____8821 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8821.FStar_Syntax_Syntax.n  in
                                 match uu____8820 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8833) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8861 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8861 with
                                      | (a',uu____8871)::bs1 ->
                                          let uu____8891 =
                                            let uu____8892 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8892
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8990 =
                                            let uu____9003 =
                                              let uu____9006 =
                                                let uu____9007 =
                                                  let uu____9014 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____9014)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____9007
                                                 in
                                              [uu____9006]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____9003
                                             in
                                          FStar_All.pipe_right uu____8891
                                            uu____8990)
                                 | uu____9029 ->
                                     let uu____9030 =
                                       let uu____9036 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____9036)
                                        in
                                     FStar_Errors.raise_error uu____9030 r
                                  in
                               let uu____9048 =
                                 let uu____9059 =
                                   let uu____9064 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____9071 =
                                     let uu____9072 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9072
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____9064 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____9071
                                    in
                                 match uu____9059 with
                                 | (f_sort,g1) ->
                                     ((let uu____9094 =
                                         FStar_Syntax_Print.term_to_string
                                           f_sort
                                          in
                                       FStar_Util.print1
                                         "In layered lift, f_sort is: %s\n\n"
                                         uu____9094);
                                      (let uu____9097 =
                                         let uu____9104 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             f_sort
                                            in
                                         FStar_All.pipe_right uu____9104
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____9097, g1)))
                                  in
                               (match uu____9048 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9171 =
                                      let uu____9176 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9177 =
                                        let uu____9178 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9178
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9176 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9177
                                       in
                                    (match uu____9171 with
                                     | (repr,g_repr) ->
                                         let uu____9195 =
                                           let uu____9198 =
                                             let uu____9201 =
                                               let uu____9204 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9204
                                                 (fun _9207  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9207)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9201
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9198
                                            in
                                         let uu____9208 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9195, uu____9208)))
                            in
                         match uu____8760 with
                         | (k,g_k) ->
                             ((let uu____9218 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9218
                               then
                                 let uu____9223 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9223
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9232 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9232
                                then
                                  let uu____9237 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9237
                                else ());
                               (let uu____9242 =
                                  let uu____9255 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9255 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9282 =
                                            let uu____9288 =
                                              let uu____9290 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9292 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9294 =
                                                let uu____9296 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9296
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9303 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9290 uu____9292
                                                uu____9294 uu____9303
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9288)
                                             in
                                          FStar_Errors.raise_error uu____9282
                                            r)
                                       else ();
                                       (let uu____9309 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9318 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9318 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9309
                                        then
                                          let uu____9335 =
                                            let uu____9338 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9338
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9335)
                                        else
                                          (let uu____9349 =
                                             let uu____9355 =
                                               let uu____9357 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9359 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9361 =
                                                 let uu____9363 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9363
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9370 =
                                                 let uu____9372 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9372
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9379 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9357 uu____9359
                                                 uu____9361 uu____9370
                                                 uu____9379
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9355)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9349 r)))
                                   in
                                match uu____9242 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___989_9411 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___989_9411.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___989_9411.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9421 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9421
                                      then
                                        let uu____9426 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9426
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
        let is_layered1 =
          let uu____9449 =
            let uu____9470 =
              FStar_TypeChecker_Env.effect_decl_opt env
                sub1.FStar_Syntax_Syntax.source
               in
            let uu____9479 =
              FStar_TypeChecker_Env.effect_decl_opt env
                sub1.FStar_Syntax_Syntax.target
               in
            (uu____9470, uu____9479)  in
          match uu____9449 with
          | (source_md_opt,target_md_opt) ->
              (match (source_md_opt, target_md_opt) with
               | (FStar_Pervasives_Native.Some
                  (src,uu____9557),FStar_Pervasives_Native.Some
                  (tgt,uu____9559)) ->
                   (FStar_Syntax_Util.is_layered src) ||
                     (FStar_Syntax_Util.is_layered tgt)
               | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
                  (tgt,uu____9597)) ->
                   ((let uu____9631 =
                       let uu____9633 = FStar_Syntax_Util.is_layered tgt  in
                       Prims.op_Negation uu____9633  in
                     if uu____9631
                     then
                       let uu____9636 =
                         let uu____9642 =
                           FStar_Util.format2
                             "For lift %s~>%s, source seems to be an effect abbreviation, in that case, target must be a layered effect"
                             (sub1.FStar_Syntax_Syntax.source).FStar_Ident.str
                             (sub1.FStar_Syntax_Syntax.target).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____9642)
                          in
                       let uu____9646 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_Errors.raise_error uu____9636 uu____9646
                     else ());
                    true)
               | (uu____9650,uu____9651) ->
                   let uu____9684 =
                     let uu____9690 =
                       FStar_Util.format2
                         "For lift %s~>%s, effect abbreviations are not allowed"
                         (sub1.FStar_Syntax_Syntax.source).FStar_Ident.str
                         (sub1.FStar_Syntax_Syntax.target).FStar_Ident.str
                        in
                     (FStar_Errors.Fatal_UnexpectedEffect, uu____9690)  in
                   let uu____9694 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error uu____9684 uu____9694)
           in
        if is_layered1
        then tc_layered_lift env sub1
        else
          (let uu____9699 =
             let uu____9706 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9706
              in
           match uu____9699 with
           | (a,wp_a_src) ->
               let uu____9713 =
                 let uu____9720 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9720
                  in
               (match uu____9713 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9728 =
                        let uu____9731 =
                          let uu____9732 =
                            let uu____9739 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9739)  in
                          FStar_Syntax_Syntax.NT uu____9732  in
                        [uu____9731]  in
                      FStar_Syntax_Subst.subst uu____9728 wp_b_tgt  in
                    let expected_k =
                      let uu____9747 =
                        let uu____9756 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9763 =
                          let uu____9772 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9772]  in
                        uu____9756 :: uu____9763  in
                      let uu____9797 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9747 uu____9797  in
                    let repr_type eff_name a1 wp =
                      (let uu____9819 =
                         let uu____9821 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9821  in
                       if uu____9819
                       then
                         let uu____9824 =
                           let uu____9830 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9830)
                            in
                         let uu____9834 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9824 uu____9834
                       else ());
                      (let uu____9837 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9837 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9870 =
                               let uu____9871 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9871
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9870
                              in
                           let uu____9878 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9879 =
                             let uu____9886 =
                               let uu____9887 =
                                 let uu____9904 =
                                   let uu____9915 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9924 =
                                     let uu____9935 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9935]  in
                                   uu____9915 :: uu____9924  in
                                 (repr, uu____9904)  in
                               FStar_Syntax_Syntax.Tm_app uu____9887  in
                             FStar_Syntax_Syntax.mk uu____9886  in
                           uu____9879 FStar_Pervasives_Native.None uu____9878)
                       in
                    let uu____9980 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____10153 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10164 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____10164 with
                              | (usubst,uvs1) ->
                                  let uu____10187 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10188 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10187, uu____10188)
                            else (env, lift_wp)  in
                          (match uu____10153 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10238 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10238))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10309 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10324 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10324 with
                              | (usubst,uvs) ->
                                  let uu____10349 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10349)
                            else ([], lift)  in
                          (match uu____10309 with
                           | (uvs,lift1) ->
                               ((let uu____10385 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10385
                                 then
                                   let uu____10389 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10389
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10395 =
                                   let uu____10402 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10402 lift1
                                    in
                                 match uu____10395 with
                                 | (lift2,comp,uu____10427) ->
                                     let uu____10428 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10428 with
                                      | (uu____10457,lift_wp,lift_elab) ->
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
                                            let uu____10489 =
                                              let uu____10500 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10500
                                               in
                                            let uu____10517 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10489, uu____10517)
                                          else
                                            (let uu____10546 =
                                               let uu____10557 =
                                                 let uu____10566 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10566)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10557
                                                in
                                             let uu____10581 =
                                               let uu____10590 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10590)  in
                                             (uu____10546, uu____10581))))))
                       in
                    (match uu____9980 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1091_10654 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1091_10654.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1091_10654.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1091_10654.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1091_10654.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1091_10654.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1091_10654.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1091_10654.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1091_10654.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1091_10654.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1091_10654.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1091_10654.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1091_10654.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1091_10654.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1091_10654.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1091_10654.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1091_10654.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1091_10654.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1091_10654.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1091_10654.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1091_10654.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1091_10654.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1091_10654.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1091_10654.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1091_10654.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1091_10654.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1091_10654.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1091_10654.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1091_10654.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1091_10654.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1091_10654.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1091_10654.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1091_10654.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1091_10654.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1091_10654.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1091_10654.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1091_10654.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1091_10654.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1091_10654.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1091_10654.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1091_10654.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1091_10654.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1091_10654.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1091_10654.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1091_10654.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10687 =
                                 let uu____10692 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10692 with
                                 | (usubst,uvs1) ->
                                     let uu____10715 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10716 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10715, uu____10716)
                                  in
                               (match uu____10687 with
                                | (env2,lift2) ->
                                    let uu____10721 =
                                      let uu____10728 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10728
                                       in
                                    (match uu____10721 with
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
                                             let uu____10754 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10755 =
                                               let uu____10762 =
                                                 let uu____10763 =
                                                   let uu____10780 =
                                                     let uu____10791 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10800 =
                                                       let uu____10811 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10811]  in
                                                     uu____10791 ::
                                                       uu____10800
                                                      in
                                                   (lift_wp1, uu____10780)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10763
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10762
                                                in
                                             uu____10755
                                               FStar_Pervasives_Native.None
                                               uu____10754
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10859 =
                                             let uu____10868 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10875 =
                                               let uu____10884 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10891 =
                                                 let uu____10900 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10900]  in
                                               uu____10884 :: uu____10891  in
                                             uu____10868 :: uu____10875  in
                                           let uu____10931 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10859 uu____10931
                                            in
                                         let uu____10934 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10934 with
                                          | (expected_k2,uu____10944,uu____10945)
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
                                                   let uu____10953 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10953))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10961 =
                             let uu____10963 =
                               let uu____10965 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10965
                                 FStar_List.length
                                in
                             uu____10963 <> Prims.int_one  in
                           if uu____10961
                           then
                             let uu____10988 =
                               let uu____10994 =
                                 let uu____10996 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10998 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____11000 =
                                   let uu____11002 =
                                     let uu____11004 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11004
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____11002
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10996 uu____10998 uu____11000
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10994)
                                in
                             FStar_Errors.raise_error uu____10988 r
                           else ());
                          (let uu____11031 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____11034 =
                                  let uu____11036 =
                                    let uu____11039 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____11039
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____11036
                                    FStar_List.length
                                   in
                                uu____11034 <> Prims.int_one)
                              in
                           if uu____11031
                           then
                             let uu____11078 =
                               let uu____11084 =
                                 let uu____11086 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____11088 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____11090 =
                                   let uu____11092 =
                                     let uu____11094 =
                                       let uu____11097 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____11097
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11094
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____11092
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11086 uu____11088 uu____11090
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____11084)
                                in
                             FStar_Errors.raise_error uu____11078 r
                           else ());
                          (let uu___1128_11139 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1128_11139.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1128_11139.FStar_Syntax_Syntax.target);
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
    fun uu____11170  ->
      fun r  ->
        match uu____11170 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11193 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11221 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11221 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11252 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11252 c  in
                     let uu____11261 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11261, uvs1, tps1, c1))
               in
            (match uu____11193 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11281 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11281 with
                  | (tps2,c2) ->
                      let uu____11296 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11296 with
                       | (tps3,env3,us) ->
                           let uu____11314 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11314 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11340)::uu____11341 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11360 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11368 =
                                    let uu____11370 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11370  in
                                  if uu____11368
                                  then
                                    let uu____11373 =
                                      let uu____11379 =
                                        let uu____11381 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11383 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11381 uu____11383
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11379)
                                       in
                                    FStar_Errors.raise_error uu____11373 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11391 =
                                    let uu____11392 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11392
                                     in
                                  match uu____11391 with
                                  | (uvs2,t) ->
                                      let uu____11421 =
                                        let uu____11426 =
                                          let uu____11439 =
                                            let uu____11440 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11440.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11439)  in
                                        match uu____11426 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11455,c5)) -> ([], c5)
                                        | (uu____11497,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11536 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11421 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11568 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11568 with
                                               | (uu____11573,t1) ->
                                                   let uu____11575 =
                                                     let uu____11581 =
                                                       let uu____11583 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11585 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11589 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11583
                                                         uu____11585
                                                         uu____11589
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11581)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11575 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  