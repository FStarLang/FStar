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
                  let repr_ts =
                    let uu____970 = repr  in
                    match uu____970 with | (us,t,uu____985) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1035 =
                    let uu____1041 =
                      let uu____1043 = FStar_Util.string_of_int n1  in
                      let uu____1045 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1047 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1043 uu____1045 uu____1047
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1041)  in
                  FStar_Errors.raise_error uu____1035 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1077 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1077 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1105 =
                    check_and_gen "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1105 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1129 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1129 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           let uu____1149 = fresh_a_and_u_a "a"  in
                           (match uu____1149 with
                            | (a,u_a) ->
                                let rest_bs =
                                  let uu____1178 =
                                    let uu____1179 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1179.FStar_Syntax_Syntax.n  in
                                  match uu____1178 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1191) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1219 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1219 with
                                       | (a',uu____1229)::bs1 ->
                                           let uu____1249 =
                                             let uu____1250 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - Prims.int_one))
                                                in
                                             FStar_All.pipe_right uu____1250
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____1348 =
                                             let uu____1361 =
                                               let uu____1364 =
                                                 let uu____1365 =
                                                   let uu____1372 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a)
                                                      in
                                                   (a', uu____1372)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1365
                                                  in
                                               [uu____1364]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1361
                                              in
                                           FStar_All.pipe_right uu____1249
                                             uu____1348)
                                  | uu____1387 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs =
                                  let uu____1399 =
                                    let uu____1408 =
                                      let uu____1417 = fresh_x_a "x" a  in
                                      [uu____1417]  in
                                    FStar_List.append rest_bs uu____1408  in
                                  a :: uu____1399  in
                                let uu____1449 =
                                  let uu____1454 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1455 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1454 u_a uu____1455  in
                                (match uu____1449 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1475 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1475
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1480 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1480);
                                      (let uu____1481 =
                                         let uu____1484 =
                                           FStar_All.pipe_right k
                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                env)
                                            in
                                         FStar_Syntax_Subst.close_univ_vars
                                           us uu____1484
                                          in
                                       (ret_us, ret_t, uu____1481))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1511 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1511 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1523 =
                     check_and_gen "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1523 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1547 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1547 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1567 = fresh_a_and_u_a "a"  in
                            (match uu____1567 with
                             | (a,u_a) ->
                                 let uu____1587 = fresh_a_and_u_a "b"  in
                                 (match uu____1587 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1616 =
                                          let uu____1617 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1617.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1616 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1629) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1657 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1657 with
                                             | (a',uu____1667)::(b',uu____1669)::bs1
                                                 ->
                                                 let uu____1699 =
                                                   let uu____1700 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1700
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1798 =
                                                   let uu____1811 =
                                                     let uu____1814 =
                                                       let uu____1815 =
                                                         let uu____1822 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1822)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1815
                                                        in
                                                     let uu____1829 =
                                                       let uu____1832 =
                                                         let uu____1833 =
                                                           let uu____1840 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1840)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1833
                                                          in
                                                       [uu____1832]  in
                                                     uu____1814 :: uu____1829
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1811
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1699 uu____1798)
                                        | uu____1855 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1879 =
                                        let uu____1890 =
                                          let uu____1895 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1896 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1895 u_a
                                            uu____1896
                                           in
                                        match uu____1890 with
                                        | (repr1,g) ->
                                            let uu____1911 =
                                              let uu____1918 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____1918
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____1911, g)
                                         in
                                      (match uu____1879 with
                                       | (f,guard_f) ->
                                           let uu____1958 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____1971 =
                                               let uu____1976 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____1995 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____1976 u_b
                                                 uu____1995
                                                in
                                             match uu____1971 with
                                             | (repr1,g) ->
                                                 let uu____2010 =
                                                   let uu____2017 =
                                                     let uu____2018 =
                                                       let uu____2019 =
                                                         let uu____2022 =
                                                           let uu____2025 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____2025
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____2022
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____2019
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____2018
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2017
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____2010, g)
                                              in
                                           (match uu____1958 with
                                            | (g,guard_g) ->
                                                let uu____2077 =
                                                  let uu____2082 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2083 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2082 u_b
                                                    uu____2083
                                                   in
                                                (match uu____2077 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2103 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2103
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
                                                      (let uu____2132 =
                                                         let uu____2135 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           bind_us uu____2135
                                                          in
                                                       (bind_us, bind_t,
                                                         uu____2132)))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2162 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2162 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2190 =
                      check_and_gen "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2190 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2215 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2215
                          then
                            let uu____2220 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2226 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2220 uu____2226
                          else ());
                         (let uu____2235 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2235 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2255 = fresh_a_and_u_a "a"  in
                              (match uu____2255 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2284 =
                                       let uu____2285 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2285.FStar_Syntax_Syntax.n  in
                                     match uu____2284 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2297) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2325 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2325 with
                                          | (a',uu____2335)::bs1 ->
                                              let uu____2355 =
                                                let uu____2356 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2356
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2454 =
                                                let uu____2467 =
                                                  let uu____2470 =
                                                    let uu____2471 =
                                                      let uu____2478 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2478)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2471
                                                     in
                                                  [uu____2470]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2467
                                                 in
                                              FStar_All.pipe_right uu____2355
                                                uu____2454)
                                     | uu____2493 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2511 =
                                     let uu____2522 =
                                       let uu____2527 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2528 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2527 u uu____2528
                                        in
                                     match uu____2522 with
                                     | (repr1,g) ->
                                         let uu____2543 =
                                           let uu____2550 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2550
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2543, g)
                                      in
                                   (match uu____2511 with
                                    | (f,guard_f) ->
                                        let uu____2590 =
                                          let uu____2595 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2596 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2595 u
                                            uu____2596
                                           in
                                        (match uu____2590 with
                                         | (ret_t,guard_ret_t) ->
                                             let pure_wp_t =
                                               let pure_wp_ts =
                                                 let uu____2615 =
                                                   FStar_TypeChecker_Env.lookup_definition
                                                     [FStar_TypeChecker_Env.NoDelta]
                                                     env
                                                     FStar_Parser_Const.pure_wp_lid
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2615 FStar_Util.must
                                                  in
                                               let uu____2620 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   pure_wp_ts
                                                  in
                                               match uu____2620 with
                                               | (uu____2625,pure_wp_t) ->
                                                   let uu____2627 =
                                                     let uu____2632 =
                                                       let uu____2633 =
                                                         FStar_All.pipe_right
                                                           ret_t
                                                           FStar_Syntax_Syntax.as_arg
                                                          in
                                                       [uu____2633]  in
                                                     FStar_Syntax_Syntax.mk_Tm_app
                                                       pure_wp_t uu____2632
                                                      in
                                                   uu____2627
                                                     FStar_Pervasives_Native.None
                                                     r
                                                in
                                             let uu____2666 =
                                               let reason =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               let uu____2682 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r uu____2682
                                                 pure_wp_t
                                                in
                                             (match uu____2666 with
                                              | (pure_wp_uvar,uu____2696,guard_wp)
                                                  ->
                                                  let c =
                                                    let uu____2711 =
                                                      let uu____2712 =
                                                        let uu____2713 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2713]  in
                                                      let uu____2714 =
                                                        let uu____2725 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2725]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2712;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2714;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2711
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2780 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2780
                                                    then
                                                      let uu____2785 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2785
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
                                                     let uu____2793 =
                                                       let uu____2796 =
                                                         FStar_All.pipe_right
                                                           k1
                                                           (FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Env.Beta;
                                                              FStar_TypeChecker_Env.Eager_unfolding]
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2796
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            stronger_us)
                                                        in
                                                     (stronger_us,
                                                       stronger_t,
                                                       uu____2793))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2825 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2825 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2853 =
                       check_and_gen "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2853 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2877 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2877 with
                          | (us,t) ->
                              let uu____2896 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2896 with
                               | (uu____2913,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2916 = fresh_a_and_u_a "a"  in
                                   (match uu____2916 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2945 =
                                            let uu____2946 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2946.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2945 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2958) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2986 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2986 with
                                               | (a',uu____2996)::bs1 ->
                                                   let uu____3016 =
                                                     let uu____3017 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3017
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3115 =
                                                     let uu____3128 =
                                                       let uu____3131 =
                                                         let uu____3132 =
                                                           let uu____3139 =
                                                             let uu____3142 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3142
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3139)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3132
                                                          in
                                                       [uu____3131]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3128
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3016 uu____3115)
                                          | uu____3163 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3181 =
                                          let uu____3192 =
                                            let uu____3197 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3198 =
                                              let uu____3199 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3199
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3197 u_a
                                              uu____3198
                                             in
                                          match uu____3192 with
                                          | (repr1,g) ->
                                              let uu____3220 =
                                                let uu____3227 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3227
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3220, g)
                                           in
                                        (match uu____3181 with
                                         | (f_bs,guard_f) ->
                                             let uu____3267 =
                                               let uu____3278 =
                                                 let uu____3283 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3284 =
                                                   let uu____3285 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3285
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3283 u_a
                                                   uu____3284
                                                  in
                                               match uu____3278 with
                                               | (repr1,g) ->
                                                   let uu____3306 =
                                                     let uu____3313 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3313
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3306, g)
                                                in
                                             (match uu____3267 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3360 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3360
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3368 =
                                                    let uu____3373 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3392 =
                                                      let uu____3393 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3393
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3373
                                                      u_a uu____3392
                                                     in
                                                  (match uu____3368 with
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
                                                        (let uu____3453 =
                                                           let uu____3456 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env)
                                                              in
                                                           FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us
                                                             uu____3456
                                                            in
                                                         (if_then_else_us,
                                                           uu____3453,
                                                           if_then_else_ty)))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3467 =
                        let uu____3470 =
                          let uu____3479 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3479 FStar_Util.must  in
                        FStar_All.pipe_right uu____3470
                          FStar_Pervasives_Native.snd
                         in
                      uu____3467.FStar_Syntax_Syntax.pos  in
                    let uu____3508 = if_then_else1  in
                    match uu____3508 with
                    | (ite_us,ite_t,uu____3523) ->
                        let uu____3536 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3536 with
                         | (us,ite_t1) ->
                             let uu____3543 =
                               let uu____3554 =
                                 let uu____3555 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3555.FStar_Syntax_Syntax.n  in
                               match uu____3554 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3569,uu____3570) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3596 =
                                     let uu____3603 =
                                       let uu____3606 =
                                         let uu____3609 =
                                           let uu____3618 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3618
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3609
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3606
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3603
                                       (fun l  ->
                                          let uu____3762 = l  in
                                          match uu____3762 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3596 with
                                    | (f,g,p) ->
                                        let uu____3787 =
                                          let uu____3788 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3788 bs1
                                           in
                                        let uu____3789 =
                                          let uu____3790 =
                                            let uu____3795 =
                                              let uu____3796 =
                                                let uu____3799 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3799
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3796
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3795
                                             in
                                          uu____3790
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3787, uu____3789, f, g, p))
                               | uu____3826 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3543 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3843 =
                                    let uu____3852 = stronger_repr  in
                                    match uu____3852 with
                                    | (uu____3873,subcomp_t,subcomp_ty) ->
                                        let uu____3888 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3888 with
                                         | (uu____3901,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3912 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3912 with
                                               | (uu____3925,subcomp_ty1) ->
                                                   let uu____3927 =
                                                     let uu____3928 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3928.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3927 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3940) ->
                                                        let uu____3961 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3961
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4067 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4085 =
                                                 let uu____4090 =
                                                   let uu____4091 =
                                                     let uu____4094 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4114 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4094 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4091
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4090
                                                  in
                                               uu____4085
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4123 = aux f_t  in
                                             let uu____4126 = aux g_t  in
                                             (uu____4123, uu____4126))
                                     in
                                  (match uu____3843 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4143 =
                                         let aux t =
                                           let uu____4160 =
                                             let uu____4167 =
                                               let uu____4168 =
                                                 let uu____4195 =
                                                   let uu____4212 =
                                                     let uu____4221 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4221
                                                      in
                                                   (uu____4212,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4195,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4168
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4167
                                              in
                                           uu____4160
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4262 = aux subcomp_f  in
                                         let uu____4263 = aux subcomp_g  in
                                         (uu____4262, uu____4263)  in
                                       (match uu____4143 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4267 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4267
                                              then
                                                let uu____4272 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4274 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4272 uu____4274
                                              else ());
                                             (let uu____4279 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4279 with
                                              | (uu____4286,uu____4287,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4290 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4290 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4292 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4292 with
                                                    | (uu____4299,uu____4300,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4306 =
                                                              let uu____4311
                                                                =
                                                                let uu____4312
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4312
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4313
                                                                =
                                                                let uu____4314
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4314]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4311
                                                                uu____4313
                                                               in
                                                            uu____4306
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4347 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4347 g_g
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
                        (let uu____4371 =
                           let uu____4377 =
                             let uu____4379 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4379
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4377)
                            in
                         FStar_Errors.raise_error uu____4371 r)
                      else ();
                      (let uu____4386 =
                         let uu____4391 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4391 with
                         | (usubst,us) ->
                             let uu____4414 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4415 =
                               let uu___413_4416 = act  in
                               let uu____4417 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4418 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___413_4416.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___413_4416.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___413_4416.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4417;
                                 FStar_Syntax_Syntax.action_typ = uu____4418
                               }  in
                             (uu____4414, uu____4415)
                          in
                       match uu____4386 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4422 =
                               let uu____4423 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4423.FStar_Syntax_Syntax.n  in
                             match uu____4422 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4449 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4449
                                 then
                                   let repr_ts =
                                     let uu____4453 = repr  in
                                     match uu____4453 with
                                     | (us,t,uu____4468) -> (us, t)  in
                                   let repr1 =
                                     let uu____4486 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4486
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4498 =
                                       let uu____4503 =
                                         let uu____4504 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4504 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4503
                                        in
                                     uu____4498 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4522 =
                                       let uu____4525 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4525
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4522
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4528 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4529 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4529 with
                            | (act_typ1,uu____4537,g_t) ->
                                let uu____4539 =
                                  let uu____4546 =
                                    let uu___438_4547 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___438_4547.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___438_4547.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___438_4547.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___438_4547.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___438_4547.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___438_4547.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___438_4547.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___438_4547.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___438_4547.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___438_4547.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___438_4547.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___438_4547.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___438_4547.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___438_4547.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___438_4547.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___438_4547.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___438_4547.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___438_4547.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___438_4547.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___438_4547.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___438_4547.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___438_4547.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___438_4547.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___438_4547.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___438_4547.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___438_4547.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___438_4547.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___438_4547.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___438_4547.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___438_4547.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___438_4547.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___438_4547.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___438_4547.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___438_4547.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___438_4547.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___438_4547.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___438_4547.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___438_4547.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___438_4547.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___438_4547.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___438_4547.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___438_4547.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___438_4547.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___438_4547.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4546
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4539 with
                                 | (act_defn,uu____4550,g_d) ->
                                     ((let uu____4553 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4553
                                       then
                                         let uu____4558 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4560 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4558 uu____4560
                                       else ());
                                      (let uu____4565 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4573 =
                                           let uu____4574 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4574.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4573 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4584) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4607 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4607 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4623 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4623 with
                                                   | (a_tm,uu____4643,g_tm)
                                                       ->
                                                       let uu____4657 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4657 with
                                                        | (repr1,g) ->
                                                            let uu____4670 =
                                                              let uu____4673
                                                                =
                                                                let uu____4676
                                                                  =
                                                                  let uu____4679
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4679
                                                                    (
                                                                    fun _4682
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4682)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4676
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4673
                                                               in
                                                            let uu____4683 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4670,
                                                              uu____4683))))
                                         | uu____4686 ->
                                             let uu____4687 =
                                               let uu____4693 =
                                                 let uu____4695 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4695
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4693)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4687 r
                                          in
                                       match uu____4565 with
                                       | (k,g_k) ->
                                           ((let uu____4712 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4712
                                             then
                                               let uu____4717 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4717
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4725 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4725
                                              then
                                                let uu____4730 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4730
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4743 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4743
                                                   in
                                                let repr_args t =
                                                  let uu____4764 =
                                                    let uu____4765 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4765.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4764 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4817 =
                                                        let uu____4818 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4818.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4817 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4827,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4837 ->
                                                           let uu____4838 =
                                                             let uu____4844 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4844)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4838 r)
                                                  | uu____4853 ->
                                                      let uu____4854 =
                                                        let uu____4860 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4860)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4854 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4870 =
                                                  let uu____4871 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4871.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4870 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4896 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4896 with
                                                     | (bs1,c1) ->
                                                         let uu____4903 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4903
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
                                                              let uu____4914
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4914))
                                                | uu____4917 ->
                                                    let uu____4918 =
                                                      let uu____4924 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4924)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4918 r
                                                 in
                                              (let uu____4928 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4928
                                               then
                                                 let uu____4933 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4933
                                               else ());
                                              (let act2 =
                                                 let uu____4939 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4939 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___511_4953 =
                                                         act1  in
                                                       let uu____4954 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___511_4953.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___511_4953.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___511_4953.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4954
                                                       }
                                                     else
                                                       (let uu____4957 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4964
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4964
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4957
                                                        then
                                                          let uu___516_4969 =
                                                            act1  in
                                                          let uu____4970 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___516_4969.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___516_4969.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___516_4969.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___516_4969.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____4970
                                                          }
                                                        else
                                                          (let uu____4973 =
                                                             let uu____4979 =
                                                               let uu____4981
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____4983
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____4981
                                                                 uu____4983
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____4979)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4973 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5008 =
                      match uu____5008 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5053 =
                        let uu____5054 = tschemes_of repr  in
                        let uu____5059 = tschemes_of return_repr  in
                        let uu____5064 = tschemes_of bind_repr  in
                        let uu____5069 = tschemes_of stronger_repr  in
                        let uu____5074 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5054;
                          FStar_Syntax_Syntax.l_return = uu____5059;
                          FStar_Syntax_Syntax.l_bind = uu____5064;
                          FStar_Syntax_Syntax.l_subcomp = uu____5069;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5074
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5053  in
                    let uu___525_5079 = ed  in
                    let uu____5080 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___525_5079.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___525_5079.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___525_5079.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___525_5079.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5087 = signature  in
                         match uu____5087 with | (us,t,uu____5102) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5080;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___525_5079.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.tscheme)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        let uu____5135 =
          FStar_TypeChecker_TcTerm.tc_check_trivial_guard env t k  in
        FStar_TypeChecker_Util.generalize_universes env uu____5135
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5157 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5157
         then
           let uu____5162 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5162
         else ());
        (let uu____5168 =
           let uu____5173 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5173 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5197 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5197  in
               let uu____5198 =
                 let uu____5205 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5205 bs  in
               (match uu____5198 with
                | (bs1,uu____5211,uu____5212) ->
                    let uu____5213 =
                      let tmp_t =
                        let uu____5223 =
                          let uu____5226 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5231  ->
                                 FStar_Pervasives_Native.Some _5231)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5226
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5223  in
                      let uu____5232 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5232 with
                      | (us,tmp_t1) ->
                          let uu____5249 =
                            let uu____5250 =
                              let uu____5251 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5251
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5250
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5249)
                       in
                    (match uu____5213 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5288 ->
                              let uu____5291 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5298 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5298 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5291
                              then (us, bs2)
                              else
                                (let uu____5309 =
                                   let uu____5315 =
                                     let uu____5317 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5319 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5317 uu____5319
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5315)
                                    in
                                 let uu____5323 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5309
                                   uu____5323))))
            in
         match uu____5168 with
         | (us,bs) ->
             let ed1 =
               let uu___562_5331 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___562_5331.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___562_5331.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___562_5331.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___562_5331.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___562_5331.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___562_5331.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5332 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5332 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5351 =
                    let uu____5356 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5356  in
                  (match uu____5351 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5377 =
                           match uu____5377 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5397 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5397 t  in
                               let uu____5406 =
                                 let uu____5407 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5407 t1  in
                               (us1, uu____5406)
                            in
                         let uu___576_5412 = ed1  in
                         let uu____5413 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5414 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5415 =
                           FStar_List.map
                             (fun a  ->
                                let uu___579_5423 = a  in
                                let uu____5424 =
                                  let uu____5425 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5425  in
                                let uu____5436 =
                                  let uu____5437 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5437  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___579_5423.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___579_5423.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___579_5423.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___579_5423.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5424;
                                  FStar_Syntax_Syntax.action_typ = uu____5436
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___576_5412.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___576_5412.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___576_5412.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___576_5412.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5413;
                           FStar_Syntax_Syntax.combinators = uu____5414;
                           FStar_Syntax_Syntax.actions = uu____5415;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___576_5412.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5449 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5449
                         then
                           let uu____5454 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5454
                         else ());
                        (let env =
                           let uu____5461 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5461
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5496 k =
                           match uu____5496 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5516 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5516 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5525 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5525 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5526 =
                                            let uu____5533 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5533 t1
                                             in
                                          (match uu____5526 with
                                           | (t2,uu____5535,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5538 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5538 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5554 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5556 =
                                                 let uu____5558 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5558
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5554 uu____5556
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5573 ->
                                               let uu____5574 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5581 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5581 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5574
                                               then (g_us, t3)
                                               else
                                                 (let uu____5592 =
                                                    let uu____5598 =
                                                      let uu____5600 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5602 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5600
                                                        uu____5602
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5598)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5592
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5610 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5610
                          then
                            let uu____5615 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5615
                          else ());
                         (let fresh_a_and_wp uu____5631 =
                            let fail1 t =
                              let uu____5644 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5644
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5660 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5660 with
                            | (uu____5671,signature1) ->
                                let uu____5673 =
                                  let uu____5674 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5674.FStar_Syntax_Syntax.n  in
                                (match uu____5673 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5684) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5713)::(wp,uu____5715)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5744 -> fail1 signature1)
                                 | uu____5745 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5759 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5759
                            then
                              let uu____5764 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5764
                            else ()  in
                          let ret_wp =
                            let uu____5770 = fresh_a_and_wp ()  in
                            match uu____5770 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5786 =
                                    let uu____5795 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5802 =
                                      let uu____5811 =
                                        let uu____5818 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5818
                                         in
                                      [uu____5811]  in
                                    uu____5795 :: uu____5802  in
                                  let uu____5837 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5786
                                    uu____5837
                                   in
                                let uu____5840 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5840
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5854 = fresh_a_and_wp ()  in
                             match uu____5854 with
                             | (a,wp_sort_a) ->
                                 let uu____5867 = fresh_a_and_wp ()  in
                                 (match uu____5867 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5883 =
                                          let uu____5892 =
                                            let uu____5899 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5899
                                             in
                                          [uu____5892]  in
                                        let uu____5912 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5883
                                          uu____5912
                                         in
                                      let k =
                                        let uu____5918 =
                                          let uu____5927 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5934 =
                                            let uu____5943 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5950 =
                                              let uu____5959 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5966 =
                                                let uu____5975 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5982 =
                                                  let uu____5991 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____5991]  in
                                                uu____5975 :: uu____5982  in
                                              uu____5959 :: uu____5966  in
                                            uu____5943 :: uu____5950  in
                                          uu____5927 :: uu____5934  in
                                        let uu____6034 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5918
                                          uu____6034
                                         in
                                      let uu____6037 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6037
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6051 = fresh_a_and_wp ()  in
                              match uu____6051 with
                              | (a,wp_sort_a) ->
                                  let uu____6064 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6064 with
                                   | (t,uu____6070) ->
                                       let k =
                                         let uu____6074 =
                                           let uu____6083 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6090 =
                                             let uu____6099 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6106 =
                                               let uu____6115 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6115]  in
                                             uu____6099 :: uu____6106  in
                                           uu____6083 :: uu____6090  in
                                         let uu____6146 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6074
                                           uu____6146
                                          in
                                       let uu____6149 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6149
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6163 = fresh_a_and_wp ()  in
                               match uu____6163 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6177 =
                                       let uu____6180 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6180
                                        in
                                     let uu____6181 =
                                       let uu____6182 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6182
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6177
                                       uu____6181
                                      in
                                   let k =
                                     let uu____6194 =
                                       let uu____6203 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6210 =
                                         let uu____6219 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6226 =
                                           let uu____6235 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6242 =
                                             let uu____6251 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6251]  in
                                           uu____6235 :: uu____6242  in
                                         uu____6219 :: uu____6226  in
                                       uu____6203 :: uu____6210  in
                                     let uu____6288 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6194
                                       uu____6288
                                      in
                                   let uu____6291 =
                                     let uu____6296 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6296
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6291
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6328 = fresh_a_and_wp ()  in
                                match uu____6328 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6344 =
                                        let uu____6353 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6360 =
                                          let uu____6369 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6369]  in
                                        uu____6353 :: uu____6360  in
                                      let uu____6394 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6344
                                        uu____6394
                                       in
                                    let uu____6397 =
                                      let uu____6402 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6402
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6397
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6418 = fresh_a_and_wp ()  in
                                 match uu____6418 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6432 =
                                         let uu____6435 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6435
                                          in
                                       let uu____6436 =
                                         let uu____6437 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6437
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6432
                                         uu____6436
                                        in
                                     let wp_sort_b_a =
                                       let uu____6449 =
                                         let uu____6458 =
                                           let uu____6465 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6465
                                            in
                                         [uu____6458]  in
                                       let uu____6478 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6449
                                         uu____6478
                                        in
                                     let k =
                                       let uu____6484 =
                                         let uu____6493 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6500 =
                                           let uu____6509 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6516 =
                                             let uu____6525 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6525]  in
                                           uu____6509 :: uu____6516  in
                                         uu____6493 :: uu____6500  in
                                       let uu____6556 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6484
                                         uu____6556
                                        in
                                     let uu____6559 =
                                       let uu____6564 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6564
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6559
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6580 = fresh_a_and_wp ()  in
                                  match uu____6580 with
                                  | (a,wp_sort_a) ->
                                      let uu____6593 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6593 with
                                       | (t,uu____6599) ->
                                           let k =
                                             let uu____6603 =
                                               let uu____6612 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6619 =
                                                 let uu____6628 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6628]  in
                                               uu____6612 :: uu____6619  in
                                             let uu____6653 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6603 uu____6653
                                              in
                                           let trivial =
                                             let uu____6657 =
                                               let uu____6662 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6662 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6657
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6677 =
                                  let uu____6694 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6694 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6723 ->
                                      let repr =
                                        let uu____6727 = fresh_a_and_wp ()
                                           in
                                        match uu____6727 with
                                        | (a,wp_sort_a) ->
                                            let uu____6740 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6740 with
                                             | (t,uu____6746) ->
                                                 let k =
                                                   let uu____6750 =
                                                     let uu____6759 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6766 =
                                                       let uu____6775 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6775]  in
                                                     uu____6759 :: uu____6766
                                                      in
                                                   let uu____6800 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6750 uu____6800
                                                    in
                                                 let uu____6803 =
                                                   let uu____6808 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6808
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6803
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6852 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6852 with
                                          | (uu____6859,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6862 =
                                                let uu____6869 =
                                                  let uu____6870 =
                                                    let uu____6887 =
                                                      let uu____6898 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6915 =
                                                        let uu____6926 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6926]  in
                                                      uu____6898 ::
                                                        uu____6915
                                                       in
                                                    (repr2, uu____6887)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6870
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6869
                                                 in
                                              uu____6862
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____6992 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____6992 wp  in
                                        let destruct_repr t =
                                          let uu____7007 =
                                            let uu____7008 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7008.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7007 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7019,(t1,uu____7021)::
                                               (wp,uu____7023)::[])
                                              -> (t1, wp)
                                          | uu____7082 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7098 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7098
                                              FStar_Util.must
                                             in
                                          let uu____7125 = fresh_a_and_wp ()
                                             in
                                          match uu____7125 with
                                          | (a,uu____7133) ->
                                              let x_a =
                                                let uu____7139 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7139
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7147 =
                                                    let uu____7152 =
                                                      let uu____7153 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7153
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7162 =
                                                      let uu____7163 =
                                                        let uu____7172 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7172
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7181 =
                                                        let uu____7192 =
                                                          let uu____7201 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7201
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7192]  in
                                                      uu____7163 ::
                                                        uu____7181
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7152 uu____7162
                                                     in
                                                  uu____7147
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7237 =
                                                  let uu____7246 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7253 =
                                                    let uu____7262 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7262]  in
                                                  uu____7246 :: uu____7253
                                                   in
                                                let uu____7287 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7237 uu____7287
                                                 in
                                              let uu____7290 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7290 with
                                               | (k1,uu____7298,uu____7299)
                                                   ->
                                                   let env1 =
                                                     let uu____7303 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7303
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
                                             let uu____7316 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7316
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7354 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7354
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7355 = fresh_a_and_wp ()
                                              in
                                           match uu____7355 with
                                           | (a,wp_sort_a) ->
                                               let uu____7368 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7368 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7384 =
                                                        let uu____7393 =
                                                          let uu____7400 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7400
                                                           in
                                                        [uu____7393]  in
                                                      let uu____7413 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7384 uu____7413
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
                                                      let uu____7421 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7421
                                                       in
                                                    let wp_g_x =
                                                      let uu____7426 =
                                                        let uu____7431 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7432 =
                                                          let uu____7433 =
                                                            let uu____7442 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7442
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7433]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7431
                                                          uu____7432
                                                         in
                                                      uu____7426
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7473 =
                                                          let uu____7478 =
                                                            let uu____7479 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7479
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7488 =
                                                            let uu____7489 =
                                                              let uu____7492
                                                                =
                                                                let uu____7495
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7496
                                                                  =
                                                                  let uu____7499
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7500
                                                                    =
                                                                    let uu____7503
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7504
                                                                    =
                                                                    let uu____7507
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7507]
                                                                     in
                                                                    uu____7503
                                                                    ::
                                                                    uu____7504
                                                                     in
                                                                  uu____7499
                                                                    ::
                                                                    uu____7500
                                                                   in
                                                                uu____7495 ::
                                                                  uu____7496
                                                                 in
                                                              r :: uu____7492
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7489
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7478
                                                            uu____7488
                                                           in
                                                        uu____7473
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7525 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7525
                                                      then
                                                        let uu____7536 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7543 =
                                                          let uu____7552 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7552]  in
                                                        uu____7536 ::
                                                          uu____7543
                                                      else []  in
                                                    let k =
                                                      let uu____7588 =
                                                        let uu____7597 =
                                                          let uu____7606 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7613 =
                                                            let uu____7622 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7622]  in
                                                          uu____7606 ::
                                                            uu____7613
                                                           in
                                                        let uu____7647 =
                                                          let uu____7656 =
                                                            let uu____7665 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7672 =
                                                              let uu____7681
                                                                =
                                                                let uu____7688
                                                                  =
                                                                  let uu____7689
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7689
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7688
                                                                 in
                                                              let uu____7690
                                                                =
                                                                let uu____7699
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7706
                                                                  =
                                                                  let uu____7715
                                                                    =
                                                                    let uu____7722
                                                                    =
                                                                    let uu____7723
                                                                    =
                                                                    let uu____7732
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7732]
                                                                     in
                                                                    let uu____7751
                                                                    =
                                                                    let uu____7754
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7754
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7723
                                                                    uu____7751
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7722
                                                                     in
                                                                  [uu____7715]
                                                                   in
                                                                uu____7699 ::
                                                                  uu____7706
                                                                 in
                                                              uu____7681 ::
                                                                uu____7690
                                                               in
                                                            uu____7665 ::
                                                              uu____7672
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7656
                                                           in
                                                        FStar_List.append
                                                          uu____7597
                                                          uu____7647
                                                         in
                                                      let uu____7799 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7588 uu____7799
                                                       in
                                                    let uu____7802 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7802 with
                                                     | (k1,uu____7810,uu____7811)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___774_7821
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___774_7821.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7823  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7823)
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
                                              (let uu____7850 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7864 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7864 with
                                                    | (usubst,uvs) ->
                                                        let uu____7887 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7888 =
                                                          let uu___787_7889 =
                                                            act  in
                                                          let uu____7890 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7891 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___787_7889.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___787_7889.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___787_7889.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7890;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7891
                                                          }  in
                                                        (uu____7887,
                                                          uu____7888))
                                                  in
                                               match uu____7850 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7895 =
                                                       let uu____7896 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7896.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7895 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7922 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7922
                                                         then
                                                           let uu____7925 =
                                                             let uu____7928 =
                                                               let uu____7929
                                                                 =
                                                                 let uu____7930
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7930
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7929
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7928
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7925
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7953 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7954 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7954 with
                                                    | (act_typ1,uu____7962,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___804_7965 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___804_7965.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7968 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7968
                                                          then
                                                            let uu____7972 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7974 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7976 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7972
                                                              uu____7974
                                                              uu____7976
                                                          else ());
                                                         (let uu____7981 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7981
                                                          with
                                                          | (act_defn,uu____7989,g_a)
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
                                                              let uu____7993
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
                                                                    let uu____8029
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8029
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8041)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8048
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8048
                                                                     in
                                                                    let uu____8051
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8051
                                                                    with
                                                                    | 
                                                                    (k1,uu____8065,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8069
                                                                    ->
                                                                    let uu____8070
                                                                    =
                                                                    let uu____8076
                                                                    =
                                                                    let uu____8078
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8080
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8078
                                                                    uu____8080
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8076)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8070
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____7993
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
                                                                    let uu____8098
                                                                    =
                                                                    let uu____8099
                                                                    =
                                                                    let uu____8100
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8100
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8099
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8098);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8102
                                                                    =
                                                                    let uu____8103
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8103.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8102
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8128
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8128
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8135
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8135
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8155
                                                                    =
                                                                    let uu____8156
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8156]
                                                                     in
                                                                    let uu____8157
                                                                    =
                                                                    let uu____8168
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8168]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8155;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8157;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8193
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8193))
                                                                    | 
                                                                    uu____8196
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8198
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8220
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8220))
                                                                     in
                                                                    match uu____8198
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
                                                                    let uu___854_8239
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___854_8239.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___854_8239.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___854_8239.FStar_Syntax_Syntax.action_params);
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
                                match uu____6677 with
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
                                      let uu____8282 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8282 ts1
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
                                          uu____8294 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8295 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8296 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___874_8299 = ed2  in
                                      let uu____8300 = cl signature  in
                                      let uu____8301 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___877_8309 = a  in
                                             let uu____8310 =
                                               let uu____8311 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8311
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8336 =
                                               let uu____8337 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8337
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___877_8309.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___877_8309.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___877_8309.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___877_8309.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8310;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8336
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___874_8299.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___874_8299.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___874_8299.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___874_8299.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8300;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8301;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___874_8299.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8363 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8363
                                      then
                                        let uu____8368 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8368
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
        let uu____8394 =
          let uu____8409 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8409 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8394 env ed quals
  
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
        let fail1 uu____8459 =
          let uu____8460 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8466 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8460 uu____8466  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8510)::(wp,uu____8512)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8541 -> fail1 ())
        | uu____8542 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8555 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8555
       then
         let uu____8560 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8560
       else ());
      (let uu____8565 =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       match uu____8565 with
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
             let uu____8598 =
               ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
                  (let uu____8602 =
                     let uu____8603 =
                       FStar_All.pipe_right src_ed
                         FStar_Syntax_Util.get_layered_effect_base
                        in
                     FStar_All.pipe_right uu____8603 FStar_Util.must  in
                   FStar_Ident.lid_equals uu____8602
                     tgt_ed.FStar_Syntax_Syntax.mname))
                 ||
                 (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered)
                     &&
                     (let uu____8612 =
                        let uu____8613 =
                          FStar_All.pipe_right tgt_ed
                            FStar_Syntax_Util.get_layered_effect_base
                           in
                        FStar_All.pipe_right uu____8613 FStar_Util.must  in
                      FStar_Ident.lid_equals uu____8612
                        src_ed.FStar_Syntax_Syntax.mname))
                    &&
                    (let uu____8621 =
                       FStar_Ident.lid_equals
                         src_ed.FStar_Syntax_Syntax.mname
                         FStar_Parser_Const.effect_PURE_lid
                        in
                     Prims.op_Negation uu____8621))
                in
             if uu____8598
             then
               let uu____8624 =
                 let uu____8630 =
                   let uu____8632 =
                     FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   let uu____8635 =
                     FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                       FStar_Ident.string_of_lid
                      in
                   FStar_Util.format2
                     "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                     uu____8632 uu____8635
                    in
                 (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8630)  in
               FStar_Errors.raise_error uu____8624 r
             else ());
            (let uu____8642 =
               if (FStar_List.length us) = Prims.int_zero
               then (env0, us, lift)
               else
                 (let uu____8666 = FStar_Syntax_Subst.open_univ_vars us lift
                     in
                  match uu____8666 with
                  | (us1,lift1) ->
                      let uu____8681 =
                        FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                      (uu____8681, us1, lift1))
                in
             match uu____8642 with
             | (env,us1,lift1) ->
                 let uu____8691 =
                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env lift1  in
                 (match uu____8691 with
                  | (lift2,lc,g) ->
                      (FStar_TypeChecker_Rel.force_trivial_guard env g;
                       (let lift_ty =
                          FStar_All.pipe_right
                            lc.FStar_TypeChecker_Common.res_typ
                            (FStar_TypeChecker_Normalize.normalize
                               [FStar_TypeChecker_Env.Beta] env0)
                           in
                        (let uu____8704 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____8704
                         then
                           let uu____8709 =
                             FStar_Syntax_Print.term_to_string lift2  in
                           let uu____8711 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.print2
                             "Typechecked lift: %s and lift_ty: %s\n"
                             uu____8709 uu____8711
                         else ());
                        (let lift_t_shape_error s =
                           let uu____8725 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.source
                              in
                           let uu____8727 =
                             FStar_Ident.string_of_lid
                               sub1.FStar_Syntax_Syntax.target
                              in
                           let uu____8729 =
                             FStar_Syntax_Print.term_to_string lift_ty  in
                           FStar_Util.format4
                             "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                             uu____8725 uu____8727 s uu____8729
                            in
                         let uu____8732 =
                           let uu____8739 =
                             let uu____8744 = FStar_Syntax_Util.type_u ()  in
                             FStar_All.pipe_right uu____8744
                               (fun uu____8761  ->
                                  match uu____8761 with
                                  | (t,u) ->
                                      let uu____8772 =
                                        let uu____8773 =
                                          FStar_Syntax_Syntax.gen_bv "a"
                                            FStar_Pervasives_Native.None t
                                           in
                                        FStar_All.pipe_right uu____8773
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____8772, u))
                              in
                           match uu____8739 with
                           | (a,u_a) ->
                               let rest_bs =
                                 let uu____8792 =
                                   let uu____8793 =
                                     FStar_Syntax_Subst.compress lift_ty  in
                                   uu____8793.FStar_Syntax_Syntax.n  in
                                 match uu____8792 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs,uu____8805) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____8833 =
                                       FStar_Syntax_Subst.open_binders bs  in
                                     (match uu____8833 with
                                      | (a',uu____8843)::bs1 ->
                                          let uu____8863 =
                                            let uu____8864 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one))
                                               in
                                            FStar_All.pipe_right uu____8864
                                              FStar_Pervasives_Native.fst
                                             in
                                          let uu____8962 =
                                            let uu____8975 =
                                              let uu____8978 =
                                                let uu____8979 =
                                                  let uu____8986 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a)
                                                     in
                                                  (a', uu____8986)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____8979
                                                 in
                                              [uu____8978]  in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____8975
                                             in
                                          FStar_All.pipe_right uu____8863
                                            uu____8962)
                                 | uu____9001 ->
                                     let uu____9002 =
                                       let uu____9008 =
                                         lift_t_shape_error
                                           "either not an arrow, or not enough binders"
                                          in
                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                         uu____9008)
                                        in
                                     FStar_Errors.raise_error uu____9002 r
                                  in
                               let uu____9020 =
                                 let uu____9031 =
                                   let uu____9036 =
                                     FStar_TypeChecker_Env.push_binders env
                                       (a :: rest_bs)
                                      in
                                   let uu____9043 =
                                     let uu____9044 =
                                       FStar_All.pipe_right a
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____9044
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   FStar_TypeChecker_Util.fresh_effect_repr_en
                                     uu____9036 r
                                     sub1.FStar_Syntax_Syntax.source u_a
                                     uu____9043
                                    in
                                 match uu____9031 with
                                 | (f_sort,g1) ->
                                     let uu____9065 =
                                       let uu____9072 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None
                                           f_sort
                                          in
                                       FStar_All.pipe_right uu____9072
                                         FStar_Syntax_Syntax.mk_binder
                                        in
                                     (uu____9065, g1)
                                  in
                               (match uu____9020 with
                                | (f_b,g_f_b) ->
                                    let bs = a ::
                                      (FStar_List.append rest_bs [f_b])  in
                                    let uu____9139 =
                                      let uu____9144 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9145 =
                                        let uu____9146 =
                                          FStar_All.pipe_right a
                                            FStar_Pervasives_Native.fst
                                           in
                                        FStar_All.pipe_right uu____9146
                                          FStar_Syntax_Syntax.bv_to_name
                                         in
                                      FStar_TypeChecker_Util.fresh_effect_repr_en
                                        uu____9144 r
                                        sub1.FStar_Syntax_Syntax.target u_a
                                        uu____9145
                                       in
                                    (match uu____9139 with
                                     | (repr,g_repr) ->
                                         let uu____9163 =
                                           let uu____9166 =
                                             let uu____9169 =
                                               let uu____9172 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               FStar_All.pipe_right
                                                 uu____9172
                                                 (fun _9175  ->
                                                    FStar_Pervasives_Native.Some
                                                      _9175)
                                                in
                                             FStar_Syntax_Syntax.mk_Total'
                                               repr uu____9169
                                              in
                                           FStar_Syntax_Util.arrow bs
                                             uu____9166
                                            in
                                         let uu____9176 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         (uu____9163, uu____9176)))
                            in
                         match uu____8732 with
                         | (k,g_k) ->
                             ((let uu____9186 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug env)
                                   (FStar_Options.Other "LayeredEffects")
                                  in
                               if uu____9186
                               then
                                 let uu____9191 =
                                   FStar_Syntax_Print.term_to_string k  in
                                 FStar_Util.print1
                                   "tc_layered_lift: before unification k: %s\n"
                                   uu____9191
                               else ());
                              (let g1 =
                                 FStar_TypeChecker_Rel.teq env lift_ty k  in
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g_k;
                               FStar_TypeChecker_Rel.force_trivial_guard env
                                 g1;
                               (let uu____9200 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env0)
                                    (FStar_Options.Other "LayeredEffects")
                                   in
                                if uu____9200
                                then
                                  let uu____9205 =
                                    FStar_Syntax_Print.term_to_string k  in
                                  FStar_Util.print1
                                    "After unification k: %s\n" uu____9205
                                else ());
                               (let uu____9210 =
                                  let uu____9223 =
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 lift2
                                     in
                                  match uu____9223 with
                                  | (inst_us,lift3) ->
                                      (if
                                         (FStar_List.length inst_us) <>
                                           Prims.int_one
                                       then
                                         (let uu____9250 =
                                            let uu____9256 =
                                              let uu____9258 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.source
                                                 in
                                              let uu____9260 =
                                                FStar_Ident.string_of_lid
                                                  sub1.FStar_Syntax_Syntax.target
                                                 in
                                              let uu____9262 =
                                                let uu____9264 =
                                                  FStar_All.pipe_right
                                                    inst_us FStar_List.length
                                                   in
                                                FStar_All.pipe_right
                                                  uu____9264
                                                  FStar_Util.string_of_int
                                                 in
                                              let uu____9271 =
                                                FStar_Syntax_Print.term_to_string
                                                  lift3
                                                 in
                                              FStar_Util.format4
                                                "Expected lift %s~>%s to be polymorphic in one universe, found:%s (t:%s)"
                                                uu____9258 uu____9260
                                                uu____9262 uu____9271
                                               in
                                            (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                              uu____9256)
                                             in
                                          FStar_Errors.raise_error uu____9250
                                            r)
                                       else ();
                                       (let uu____9277 =
                                          ((FStar_List.length us1) =
                                             Prims.int_zero)
                                            ||
                                            (((FStar_List.length us1) =
                                                (FStar_List.length inst_us))
                                               &&
                                               (FStar_List.forall2
                                                  (fun u1  ->
                                                     fun u2  ->
                                                       let uu____9286 =
                                                         FStar_Syntax_Syntax.order_univ_name
                                                           u1 u2
                                                          in
                                                       uu____9286 =
                                                         Prims.int_zero) us1
                                                  inst_us))
                                           in
                                        if uu____9277
                                        then
                                          let uu____9303 =
                                            let uu____9306 =
                                              FStar_All.pipe_right k
                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                   env)
                                               in
                                            FStar_All.pipe_right uu____9306
                                              (FStar_Syntax_Subst.close_univ_vars
                                                 inst_us)
                                             in
                                          (inst_us, lift3, uu____9303)
                                        else
                                          (let uu____9317 =
                                             let uu____9323 =
                                               let uu____9325 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.source
                                                  in
                                               let uu____9327 =
                                                 FStar_Ident.string_of_lid
                                                   sub1.FStar_Syntax_Syntax.target
                                                  in
                                               let uu____9329 =
                                                 let uu____9331 =
                                                   FStar_All.pipe_right us1
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9331
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9338 =
                                                 let uu____9340 =
                                                   FStar_All.pipe_right
                                                     inst_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____9340
                                                   FStar_Util.string_of_int
                                                  in
                                               let uu____9347 =
                                                 FStar_Syntax_Print.term_to_string
                                                   lift3
                                                  in
                                               FStar_Util.format5
                                                 "Annotated and generalized universes on %s~%s are not same, annotated:%s, generalized:%s (t:%s)"
                                                 uu____9325 uu____9327
                                                 uu____9329 uu____9338
                                                 uu____9347
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____9323)
                                              in
                                           FStar_Errors.raise_error
                                             uu____9317 r)))
                                   in
                                match uu____9210 with
                                | (us2,lift3,lift_wp) ->
                                    let sub2 =
                                      let uu___985_9379 = sub1  in
                                      {
                                        FStar_Syntax_Syntax.source =
                                          (uu___985_9379.FStar_Syntax_Syntax.source);
                                        FStar_Syntax_Syntax.target =
                                          (uu___985_9379.FStar_Syntax_Syntax.target);
                                        FStar_Syntax_Syntax.lift_wp =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift_wp));
                                        FStar_Syntax_Syntax.lift =
                                          (FStar_Pervasives_Native.Some
                                             (us2, lift3))
                                      }  in
                                    ((let uu____9389 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env0)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____9389
                                      then
                                        let uu____9394 =
                                          FStar_Syntax_Print.sub_eff_to_string
                                            sub2
                                           in
                                        FStar_Util.print1
                                          "Final sub_effect: %s\n" uu____9394
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
        let uu____9417 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9417
        then tc_layered_lift env sub1
        else
          (let uu____9424 =
             let uu____9431 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9431
              in
           match uu____9424 with
           | (a,wp_a_src) ->
               let uu____9438 =
                 let uu____9445 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9445
                  in
               (match uu____9438 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9453 =
                        let uu____9456 =
                          let uu____9457 =
                            let uu____9464 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9464)  in
                          FStar_Syntax_Syntax.NT uu____9457  in
                        [uu____9456]  in
                      FStar_Syntax_Subst.subst uu____9453 wp_b_tgt  in
                    let expected_k =
                      let uu____9472 =
                        let uu____9481 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9488 =
                          let uu____9497 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9497]  in
                        uu____9481 :: uu____9488  in
                      let uu____9522 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9472 uu____9522  in
                    let repr_type eff_name a1 wp =
                      (let uu____9544 =
                         let uu____9546 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9546  in
                       if uu____9544
                       then
                         let uu____9549 =
                           let uu____9555 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9555)
                            in
                         let uu____9559 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9549 uu____9559
                       else ());
                      (let uu____9562 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9562 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9595 =
                               let uu____9596 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9596
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9595
                              in
                           let uu____9603 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9604 =
                             let uu____9611 =
                               let uu____9612 =
                                 let uu____9629 =
                                   let uu____9640 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9649 =
                                     let uu____9660 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9660]  in
                                   uu____9640 :: uu____9649  in
                                 (repr, uu____9629)  in
                               FStar_Syntax_Syntax.Tm_app uu____9612  in
                             FStar_Syntax_Syntax.mk uu____9611  in
                           uu____9604 FStar_Pervasives_Native.None uu____9603)
                       in
                    let uu____9705 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9878 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9889 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9889 with
                              | (usubst,uvs1) ->
                                  let uu____9912 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9913 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9912, uu____9913)
                            else (env, lift_wp)  in
                          (match uu____9878 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9963 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9963))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10034 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10049 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10049 with
                              | (usubst,uvs) ->
                                  let uu____10074 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10074)
                            else ([], lift)  in
                          (match uu____10034 with
                           | (uvs,lift1) ->
                               ((let uu____10110 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10110
                                 then
                                   let uu____10114 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10114
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10120 =
                                   let uu____10127 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10127 lift1
                                    in
                                 match uu____10120 with
                                 | (lift2,comp,uu____10152) ->
                                     let uu____10153 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10153 with
                                      | (uu____10182,lift_wp,lift_elab) ->
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
                                            let uu____10214 =
                                              let uu____10225 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10225
                                               in
                                            let uu____10242 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10214, uu____10242)
                                          else
                                            (let uu____10271 =
                                               let uu____10282 =
                                                 let uu____10291 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10291)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10282
                                                in
                                             let uu____10306 =
                                               let uu____10315 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10315)  in
                                             (uu____10271, uu____10306))))))
                       in
                    (match uu____9705 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1065_10379 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1065_10379.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1065_10379.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1065_10379.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1065_10379.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1065_10379.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1065_10379.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1065_10379.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1065_10379.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1065_10379.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1065_10379.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1065_10379.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1065_10379.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1065_10379.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1065_10379.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1065_10379.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1065_10379.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1065_10379.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1065_10379.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1065_10379.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1065_10379.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1065_10379.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1065_10379.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1065_10379.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1065_10379.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1065_10379.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1065_10379.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1065_10379.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1065_10379.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1065_10379.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1065_10379.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1065_10379.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1065_10379.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1065_10379.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1065_10379.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1065_10379.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1065_10379.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1065_10379.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1065_10379.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1065_10379.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1065_10379.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1065_10379.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1065_10379.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1065_10379.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1065_10379.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10412 =
                                 let uu____10417 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10417 with
                                 | (usubst,uvs1) ->
                                     let uu____10440 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10441 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10440, uu____10441)
                                  in
                               (match uu____10412 with
                                | (env2,lift2) ->
                                    let uu____10446 =
                                      let uu____10453 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10453
                                       in
                                    (match uu____10446 with
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
                                             let uu____10479 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10480 =
                                               let uu____10487 =
                                                 let uu____10488 =
                                                   let uu____10505 =
                                                     let uu____10516 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10525 =
                                                       let uu____10536 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10536]  in
                                                     uu____10516 ::
                                                       uu____10525
                                                      in
                                                   (lift_wp1, uu____10505)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10488
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10487
                                                in
                                             uu____10480
                                               FStar_Pervasives_Native.None
                                               uu____10479
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10584 =
                                             let uu____10593 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10600 =
                                               let uu____10609 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10616 =
                                                 let uu____10625 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10625]  in
                                               uu____10609 :: uu____10616  in
                                             uu____10593 :: uu____10600  in
                                           let uu____10656 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10584 uu____10656
                                            in
                                         let uu____10659 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10659 with
                                          | (expected_k2,uu____10669,uu____10670)
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
                                                   let uu____10678 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10678))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10686 =
                             let uu____10688 =
                               let uu____10690 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10690
                                 FStar_List.length
                                in
                             uu____10688 <> Prims.int_one  in
                           if uu____10686
                           then
                             let uu____10713 =
                               let uu____10719 =
                                 let uu____10721 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10723 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10725 =
                                   let uu____10727 =
                                     let uu____10729 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10729
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10727
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10721 uu____10723 uu____10725
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10719)
                                in
                             FStar_Errors.raise_error uu____10713 r
                           else ());
                          (let uu____10756 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10759 =
                                  let uu____10761 =
                                    let uu____10764 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10764
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10761
                                    FStar_List.length
                                   in
                                uu____10759 <> Prims.int_one)
                              in
                           if uu____10756
                           then
                             let uu____10803 =
                               let uu____10809 =
                                 let uu____10811 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10813 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10815 =
                                   let uu____10817 =
                                     let uu____10819 =
                                       let uu____10822 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10822
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10819
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10817
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10811 uu____10813 uu____10815
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10809)
                                in
                             FStar_Errors.raise_error uu____10803 r
                           else ());
                          (let uu___1102_10864 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1102_10864.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1102_10864.FStar_Syntax_Syntax.target);
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
    fun uu____10895  ->
      fun r  ->
        match uu____10895 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10918 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10946 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10946 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10977 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10977 c  in
                     let uu____10986 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10986, uvs1, tps1, c1))
               in
            (match uu____10918 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11006 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11006 with
                  | (tps2,c2) ->
                      let uu____11021 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11021 with
                       | (tps3,env3,us) ->
                           let uu____11039 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11039 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11065)::uu____11066 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11085 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11093 =
                                    let uu____11095 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11095  in
                                  if uu____11093
                                  then
                                    let uu____11098 =
                                      let uu____11104 =
                                        let uu____11106 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11108 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11106 uu____11108
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11104)
                                       in
                                    FStar_Errors.raise_error uu____11098 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11116 =
                                    let uu____11117 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11117
                                     in
                                  match uu____11116 with
                                  | (uvs2,t) ->
                                      let uu____11146 =
                                        let uu____11151 =
                                          let uu____11164 =
                                            let uu____11165 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11165.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11164)  in
                                        match uu____11151 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11180,c5)) -> ([], c5)
                                        | (uu____11222,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11261 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11146 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11293 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11293 with
                                               | (uu____11298,t1) ->
                                                   let uu____11300 =
                                                     let uu____11306 =
                                                       let uu____11308 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11310 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11314 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11308
                                                         uu____11310
                                                         uu____11314
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11306)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11300 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  